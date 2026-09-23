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

  /* Bitmask with rejection: draw, mask to the bit width of `range`, retry
   * if too large. Terminates: the seed visits every 64-bit value and
   * `mix64` is a bijection, so a zero draw always comes. */
  uint64_t mask = UINT64_MAX >> __builtin_clzll(range);
  uint64_t seed = sm_seed(g), gamma = sm_gamma(g), x;
  do {
    seed += gamma;
    x = sm_mix64(seed) & mask;
  } while (x > range);

  return sm_pair(lean_box(base + x), sm_update(g, seed, gamma));
}
