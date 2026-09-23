/*
 * Native implementation of SplitMix64, bit-for-bit compatible with the
 * Haskell `splitmix` package. The Lean definitions in `SplitMix/Native.lean`
 * are the specification; every function here must agree with them.
 *
 * A `SplitMix` value is a Lean constructor object with no object fields and
 * 16 bytes of scalar data: `seed` at byte offset 0, `gamma` at offset 8.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <pthread.h>
#include <stdlib.h>

/* Murmur3 finalizer (Haskell `mix64`). */
static inline uint64_t sm_mix64(uint64_t z) {
  z = (z ^ (z >> 33)) * 0xff51afd7ed558ccdULL;
  z = (z ^ (z >> 33)) * 0xc4ceb9fe1a85ec53ULL;
  return z ^ (z >> 33);
}

/* Stafford variant 13 (Haskell `mix64variant13`). */
static inline uint64_t sm_mix64_variant13(uint64_t z) {
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

/* Haskell `mixGamma`: an odd gamma with enough bit transitions. */
static inline uint64_t sm_mix_gamma(uint64_t z) {
  z = sm_mix64_variant13(z) | 1;
  int n = __builtin_popcountll(z ^ (z >> 1));
  return n >= 24 ? z : z ^ 0xaaaaaaaaaaaaaaaaULL;
}

static inline uint64_t sm_seed(b_lean_obj_arg g) { return lean_ctor_get_uint64(g, 0); }
static inline uint64_t sm_gamma(b_lean_obj_arg g) { return lean_ctor_get_uint64(g, 8); }

static inline lean_obj_res sm_alloc(uint64_t seed, uint64_t gamma) {
  lean_object *g = lean_alloc_ctor(0, 0, 16);
  lean_ctor_set_uint64(g, 0, seed);
  lean_ctor_set_uint64(g, 8, gamma);
  return g;
}

/* Consumes `g`, returning a generator with the given state. Reuses `g`'s
 * memory when we hold the only reference to it. */
static inline lean_obj_res sm_update(lean_obj_arg g, uint64_t seed, uint64_t gamma) {
  if (lean_is_exclusive(g)) {
    lean_ctor_set_uint64(g, 0, seed);
    lean_ctor_set_uint64(g, 8, gamma);
    return g;
  }
  lean_dec_ref(g);
  return sm_alloc(seed, gamma);
}

static inline lean_obj_res sm_pair(lean_obj_arg a, lean_obj_arg b) {
  lean_object *p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

/* SplitMix.split : SplitMix → SplitMix × SplitMix */
LEAN_EXPORT lean_obj_res lean_splitmix_split(lean_obj_arg g) {
  uint64_t gamma = sm_gamma(g);
  uint64_t s1 = sm_seed(g) + gamma;
  uint64_t s2 = s1 + gamma;
  lean_object *right = sm_alloc(sm_mix64(s1), sm_mix_gamma(s2));
  lean_object *left = sm_update(g, s2, gamma);
  return sm_pair(left, right);
}

/* Lean fallback for ranges that don't fit in machine words (`@[export]`ed
 * from `SplitMix/Native.lean`). Takes ownership of all arguments. */
LEAN_EXPORT lean_obj_res lean_splitmix_rand_nat_slow(lean_obj_arg g, lean_obj_arg lo, lean_obj_arg hi);

/* A uniform draw from [0, range], for 0 < range < 2^63, by bitmask with
 * rejection: draw, mask to the bit width of `range`, retry if too large.
 * Terminates: the seed visits every 64-bit value and `mix64` is a bijection,
 * so a zero draw always comes. Advances `*seed`. */
static inline uint64_t sm_bounded(uint64_t *seed, uint64_t gamma, uint64_t range) {
  uint64_t mask = UINT64_MAX >> __builtin_clzll(range);
  uint64_t s = *seed, x;
  do {
    s += gamma;
    x = sm_mix64(s) & mask;
  } while (x > range);
  *seed = s;
  return x;
}

/* SplitMix.randNat : SplitMix → Nat → Nat → Nat × SplitMix */
LEAN_EXPORT lean_obj_res lean_splitmix_rand_nat(lean_obj_arg g, lean_obj_arg lo, lean_obj_arg hi) {
  if (LEAN_UNLIKELY(!lean_is_scalar(lo) || !lean_is_scalar(hi))) {
    return lean_splitmix_rand_nat_slow(g, lo, hi);
  }
  /* Both bounds are unboxed and below 2^63, so the result is too. */
  size_t l = lean_unbox(lo), h = lean_unbox(hi);
  if (l == h) return sm_pair(lo, g);
  uint64_t base = l < h ? l : h;
  uint64_t range = l < h ? h - l : l - h;
  uint64_t seed = sm_seed(g), gamma = sm_gamma(g);
  uint64_t x = sm_bounded(&seed, gamma, range);
  return sm_pair(lean_box(base + x), sm_update(g, seed, gamma));
}

/*
 * Mutable generators (`SplitMix.Gen`): a Lean external object whose data is a
 * heap-allocated `sm_gen`. Operations borrow the object and update the state
 * in place, so a draw with small bounds allocates nothing and does no
 * reference counting.
 */

typedef struct {
  uint64_t seed;
  uint64_t gamma;
} sm_gen;

static void sm_gen_finalize(void *p) { free(p); }
static void sm_gen_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }

static lean_external_class *sm_gen_class;
static pthread_once_t sm_gen_class_once = PTHREAD_ONCE_INIT;

static void sm_gen_register(void) {
  sm_gen_class = lean_register_external_class(sm_gen_finalize, sm_gen_foreach);
}

static inline sm_gen *sm_gen_of(b_lean_obj_arg g) { return (sm_gen *)lean_get_external_data(g); }

/* Every `Gen` is made here, so this is where the class is registered: once,
 * on first use, when the Lean runtime is certainly initialized. (Registering
 * in a load-time constructor crashed compiled executables, whose constructors
 * run before `main` initializes the runtime.) */
static inline lean_obj_res sm_gen_alloc(uint64_t seed, uint64_t gamma) {
  pthread_once(&sm_gen_class_once, sm_gen_register);
  sm_gen *p = malloc(sizeof(sm_gen));
  if (p == NULL) lean_internal_panic_out_of_memory();
  p->seed = seed;
  p->gamma = gamma;
  return lean_alloc_external(sm_gen_class, p);
}

/* SplitMix.Gen.new : @& SplitMix → BaseIO Gen */
LEAN_EXPORT lean_obj_res lean_splitmix_gen_new(b_lean_obj_arg s) {
  return sm_gen_alloc(sm_seed(s), sm_gamma(s));
}

/* SplitMix.Gen.get : @& Gen → BaseIO SplitMix */
LEAN_EXPORT lean_obj_res lean_splitmix_gen_get(b_lean_obj_arg g) {
  sm_gen *p = sm_gen_of(g);
  return sm_alloc(p->seed, p->gamma);
}

/* SplitMix.Gen.set : @& Gen → @& SplitMix → BaseIO Unit */
LEAN_EXPORT lean_obj_res lean_splitmix_gen_set(b_lean_obj_arg g, b_lean_obj_arg s) {
  sm_gen *p = sm_gen_of(g);
  p->seed = sm_seed(s);
  p->gamma = sm_gamma(s);
  return lean_box(0);
}

/* SplitMix.Gen.nextUInt64 : @& Gen → BaseIO UInt64 */
LEAN_EXPORT uint64_t lean_splitmix_gen_next_uint64(b_lean_obj_arg g) {
  sm_gen *p = sm_gen_of(g);
  p->seed += p->gamma;
  return sm_mix64(p->seed);
}

/* SplitMix.Gen.randNat : @& Gen → @& Nat → @& Nat → BaseIO {x : Nat // …}
 * (the subtype is erased: the result is the `Nat`). */
LEAN_EXPORT lean_obj_res lean_splitmix_gen_rand_nat(b_lean_obj_arg g, b_lean_obj_arg lo, b_lean_obj_arg hi) {
  sm_gen *p = sm_gen_of(g);
  if (LEAN_UNLIKELY(!lean_is_scalar(lo) || !lean_is_scalar(hi))) {
    /* Bignum bounds: run the Lean spec on a copy of the state, then store the
     * state it returns. */
    lean_inc(lo);
    lean_inc(hi);
    lean_object *r = lean_splitmix_rand_nat_slow(sm_alloc(p->seed, p->gamma), lo, hi);
    lean_object *x = lean_ctor_get(r, 0);
    lean_object *s = lean_ctor_get(r, 1);
    p->seed = sm_seed(s);
    p->gamma = sm_gamma(s);
    lean_inc(x);
    lean_dec_ref(r);
    return x;
  }
  size_t l = lean_unbox(lo), h = lean_unbox(hi);
  if (l == h) return lean_box(l);
  uint64_t base = l < h ? l : h;
  uint64_t range = l < h ? h - l : l - h;
  return lean_box(base + sm_bounded(&p->seed, p->gamma, range));
}

/* SplitMix.Gen.split : @& Gen → BaseIO Gen. `g` keeps the left half of
 * `splitRef`; the result is the right half. */
LEAN_EXPORT lean_obj_res lean_splitmix_gen_split(b_lean_obj_arg g) {
  sm_gen *p = sm_gen_of(g);
  uint64_t s1 = p->seed + p->gamma;
  uint64_t s2 = s1 + p->gamma;
  p->seed = s2;
  return sm_gen_alloc(sm_mix64(s1), sm_mix_gamma(s2));
}
