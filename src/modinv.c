/*                                                    -*- coding: utf-8 -*-
 * modinv.c - Multiplicative inverse by the safegcd
 *
 * Copyright (C) 2023  Free Software Initiative of Japan
 * Author: NIIBE Yutaka <gniibe@fsij.org>
 *
 * This file is a part of Gnuk, a GnuPG USB Token implementation.
 *
 * Gnuk is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Gnuk is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
 * License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
 */

/*
 * This implementation follows the explanation in the following document:
 *
 * The safegcd implementaion in libsecp256k1 explained:
 * https://github.com/bitcoin-core/secp256k1/blob/0775283/doc/safegcd_implementation.md
 *
 * While it suggests use of 62-bit integer representation for 64-bit
 * computer (and 30-bit representation for 32-bit computer), this
 * implementation uses N=31 and tweaked version of U in the transition
 * matrix, so that iteration can be 19 times for p25519.
 */

/*
 * Other references:
 *
 * [1] Daniel J. Bernstein, Bo-Yin Yang.
 *     Fast constant-time gcd and modular inversion.
 *     Date: 2019.04.13.
 *     https://gcd.cr.yp.to/papers.html#safegcd
 *
 * [2] Pieter Wuille.
 *     Bounds on divsteps iterations in safegcd.
 *     https://github.com/sipa/safegcd-bounds#readme
 */

#include <stdint.h>
#include <string.h>
#include "bn.h"

/* Representation with signed 31-bit limb for bignum integer. */
#define SR256_WORDS 9
typedef struct sr256 {
  int32_t v[SR256_WORDS];
} sr256;

/* Skip a computation with limb of zero.  */
#define MODINV_LIMBS_CANBE_SKIPPED 1

/* The modulus in signed 31-bit representation. */
static const sr256 modulus_25519 = {
  { -19, 0, 0, 0, 0, 0, 0, 0, 128 }
};
/* inv31: modulus^-1 (mod 2^31)
 * pow(modulus_25519,2**31-1,2**31)
 */
static const uint32_t modulus_inv31_25519 = 0x579435e5;

static const sr256 modulus_secp256k1 = {
  { -977, -2, 0, 0, 0, 0, 0, 0, 256 }
};

static const uint32_t modulus_inv31_secp256k1 = 0x2ddacacf;

/*
 * Data type for transition matrix
 *
 * t = [ u  v ]
 *     [ q  r ]
 *
 * u_ is tweaked by -1, so that overflow never occurs.
 */
typedef struct {
  int32_t u_, v;
  int32_t q,  r;
} matrix_2x2;

static int32_t
modinv_divsteps (int32_t zeta, uint32_t f0, uint32_t g0, matrix_2x2 *t)
{
  uint32_t f, g;
  uint32_t u, v, q, r;
  int i = 0;

  f = f0;
  g = g0;
  u = 1;
  v = 0;
  q = 0;
  r = 1;

  for (;;)
    {
      uint32_t mask1, mask2;
      uint32_t x, y, z;         /* -f, -u, -v conditionally.  */

      mask1 = zeta >> 31;
      mask2 = 0UL - (g & 1);

      x = (f ^ mask1) - mask1;
      y = (u ^ mask1) - mask1;
      z = (v ^ mask1) - mask1;

      g += x & mask2;
      q += y & mask2;
      r += z & mask2;

      mask1 &= mask2;

      zeta = (zeta ^ mask1) - 1;
      f += g & mask1;
      u += q & mask1;
      v += r & mask1;

      g >>= 1;

      if (++i >= 31)
        break;
      u <<= 1;
      v <<= 1;
    }

  t->u_ = (int32_t)(u - 1 + u); /* double minus 1 */
  t->v = (int32_t)(v << 1);     /* double */
  t->q = (int32_t)q;
  t->r = (int32_t)r;

  return zeta;
}

/*
 */
static void
modinv_update_de (sr256 *d, sr256 *e, const matrix_2x2 *t,
                  const sr256 *modulus, uint32_t inv31)
{
  const int32_t u_ = t->u_, v = t->v, q = t->q, r = t->r;
  int32_t di, ei, me, sd, se;
  int64_t cd, ce;
  int32_t md_; /* MD_ stands for MD minus 1, which keeps <= 2**31-1 */
  int i;

  sd = d->v[8] >> 31;
  se = e->v[8] >> 31;
  md_ = (u_ & sd) + (v & se);
  me = (q & sd) + (r & se);
  di = d->v[0];
  ei = e->v[0];
  cd = (int64_t)u_ * di + di + (int64_t)v * ei;
  ce = (int64_t)q * di + (int64_t)r * ei;
  /* MD_ + 1 in the following expression may never overflow in uint32_t.
   * The value of MD_ may be 2**31-1, but the addition is by unsigned.  */
  md_ -= ((uint32_t)md_ + (1 & sd) + inv31 * (uint32_t)cd) & 0x7fffffff;
  me -= (inv31 * (uint32_t)ce + me) & 0x7fffffff;
  cd += (int64_t)modulus->v[0] * md_ + (int64_t)(modulus->v[0] & sd);
  ce += (int64_t)modulus->v[0] * me;
  cd >>= 31;
  ce >>= 31;
  for (i = 1; i < SR256_WORDS; i++)
    {
      di = d->v[i];
      ei = e->v[i];
      cd += (int64_t)u_ * di + di + (int64_t)v * ei;
      ce += (int64_t)q * di + (int64_t)r * ei;
#if MODINV_LIMBS_CANBE_SKIPPED
      if (i == 1  || i == 8)
        {
#endif
          cd += (int64_t)modulus->v[i] * md_ + (int64_t)(modulus->v[i] & sd);
          ce += (int64_t)modulus->v[i] * me;
#if MODINV_LIMBS_CANBE_SKIPPED
        }
#endif
      d->v[i - 1] = (int32_t)cd & 0x7fffffff;
      e->v[i - 1] = (int32_t)ce & 0x7fffffff;
      cd >>= 31;
      ce >>= 31;
    }

  d->v[8] = (int32_t)cd;
  e->v[8] = (int32_t)ce;
}

/*
 */
static void
modinv_update_fg (sr256 *f, sr256 *g, const matrix_2x2 *t)
{
  const int32_t u_ = t->u_, v = t->v, q = t->q, r = t->r;
  int32_t fi, gi;
  int64_t cf, cg;
  int i;

  fi = f->v[0];
  gi = g->v[0];
  cf = (int64_t)u_ * fi + fi + (int64_t)v * gi;
  cg = (int64_t)q * fi + (int64_t)r * gi;
  cf >>= 31;
  cg >>= 31;

  for (i = 1; i < SR256_WORDS; i++)
    {
      fi = f->v[i];
      gi = g->v[i];
      cf += (int64_t)u_ * fi + fi + (int64_t)v * gi;
      cg += (int64_t)q * fi + (int64_t)r * gi;
      f->v[i - 1] = (int32_t)cf & 0x7fffffff;
      g->v[i - 1] = (int32_t)cg & 0x7fffffff;
      cf >>= 31;
      cg >>= 31;
    }

  f->v[8] = (int32_t)cf;
  g->v[8] = (int32_t)cg;
}


/*
 */
static void
modinv_normalize (sr256 *r, int32_t sign, const sr256 *modulus)
{
  int32_t r0, r1, r2, r3, r4, r5, r6, r7, r8;
  int32_t mask_add, mask_neg;

  r0 = r->v[0];
  r1 = r->v[1];
  r2 = r->v[2];
  r3 = r->v[3];
  r4 = r->v[4];
  r5 = r->v[5];
  r6 = r->v[6];
  r7 = r->v[7];
  r8 = r->v[8];

  /* Add the modulus if the input is negative. */
  mask_add = r8 >> 31;
  r0 += modulus->v[0] & mask_add;
  r1 += modulus->v[1] & mask_add;
#if MODINV_LIMBS_CANBE_SKIPPED
  /* We know it's zero.  */
#else
  r2 += modulus->v[2] & mask_add;
  r3 += modulus->v[3] & mask_add;
  r4 += modulus->v[4] & mask_add;
  r5 += modulus->v[5] & mask_add;
  r6 += modulus->v[6] & mask_add;
  r7 += modulus->v[7] & mask_add;
#endif
  r8 += modulus->v[8] & mask_add;

  /* negate if SIGN is negative.  */
  mask_neg = sign >> 31;
  r0 = (r0 ^ mask_neg) - mask_neg;
  r1 = (r1 ^ mask_neg) - mask_neg;
  r2 = (r2 ^ mask_neg) - mask_neg;
  r3 = (r3 ^ mask_neg) - mask_neg;
  r4 = (r4 ^ mask_neg) - mask_neg;
  r5 = (r5 ^ mask_neg) - mask_neg;
  r6 = (r6 ^ mask_neg) - mask_neg;
  r7 = (r7 ^ mask_neg) - mask_neg;
  r8 = (r8 ^ mask_neg) - mask_neg;
  r1 += r0 >> 31; r0 &= 0x7fffffff;
  r2 += r1 >> 31; r1 &= 0x7fffffff;
  r3 += r2 >> 31; r2 &= 0x7fffffff;
  r4 += r3 >> 31; r3 &= 0x7fffffff;
  r5 += r4 >> 31; r4 &= 0x7fffffff;
  r6 += r5 >> 31; r5 &= 0x7fffffff;
  r7 += r6 >> 31; r6 &= 0x7fffffff;
  r8 += r7 >> 31; r7 &= 0x7fffffff;

  /* It brings r from range (-2*modulus,modulus) to range
     (-modulus,modulus). */

  /* Add the modulus again if the result is still negative. */
  mask_add = r8 >> 31;
  r0 += modulus->v[0] & mask_add;
  r1 += modulus->v[1] & mask_add;
#if MODINV_LIMBS_CANBE_SKIPPED
  /* We know it's zero.  */
#else
  r2 += modulus->v[2] & mask_add;
  r3 += modulus->v[3] & mask_add;
  r4 += modulus->v[4] & mask_add;
  r5 += modulus->v[5] & mask_add;
  r6 += modulus->v[6] & mask_add;
  r7 += modulus->v[7] & mask_add;
#endif
  r8 += modulus->v[8] & mask_add;
  r1 += r0 >> 31; r0 &= 0x7fffffff;
  r2 += r1 >> 31; r1 &= 0x7fffffff;
  r3 += r2 >> 31; r2 &= 0x7fffffff;
  r4 += r3 >> 31; r3 &= 0x7fffffff;
  r5 += r4 >> 31; r4 &= 0x7fffffff;
  r6 += r5 >> 31; r5 &= 0x7fffffff;
  r7 += r6 >> 31; r6 &= 0x7fffffff;
  r8 += r7 >> 31; r7 &= 0x7fffffff;

  /* It brings r from range (-2*modulus,modulus) to range
     [0,modulus). */

  r->v[0] = r0;
  r->v[1] = r1;
  r->v[2] = r2;
  r->v[3] = r3;
  r->v[4] = r4;
  r->v[5] = r5;
  r->v[6] = r6;
  r->v[7] = r7;
  r->v[8] = r8;
}

/*
 */
static void
modinv (sr256 *x, const sr256 *modulus, uint32_t inv31, int iterations)
{
  sr256 d = {{0}};
  sr256 e = {{1}};
  sr256 f = *modulus;
  sr256 g = *x;
  int32_t zeta = -1;
  int i;

  for (i = 0; i < iterations; i++)
    {
      matrix_2x2 t;

      zeta = modinv_divsteps (zeta, f.v[0], g.v[0], &t);
      modinv_update_de (&d, &e, &t, modulus, inv31);
      modinv_update_fg (&f, &g, &t);
    }

  modinv_normalize (&d, f.v[8], modulus);
  *x = d;
}

static void
bn_to_signed31 (sr256 *r, const bn256 *a)
{
  uint32_t a0, a1, a2, a3, a4, a5, a6, a7;

  a0 = a->word[0];
  a1 = a->word[1];
  a2 = a->word[2];
  a3 = a->word[3];
  a4 = a->word[4];
  a5 = a->word[5];
  a6 = a->word[6];
  a7 = a->word[7];

  r->v[0] =               (a0 <<  0) & 0x7fffffff;
  r->v[1] = (a0 >> 31) | ((a1 <<  1) & 0x7fffffff);
  r->v[2] = (a1 >> 30) | ((a2 <<  2) & 0x7fffffff);
  r->v[3] = (a2 >> 29) | ((a3 <<  3) & 0x7fffffff);
  r->v[4] = (a3 >> 28) | ((a4 <<  4) & 0x7fffffff);
  r->v[5] = (a4 >> 27) | ((a5 <<  5) & 0x7fffffff);
  r->v[6] = (a5 >> 26) | ((a6 <<  6) & 0x7fffffff);
  r->v[7] = (a6 >> 25) | ((a7 <<  7) & 0x7fffffff);
  r->v[8] = (a7 >> 24);
}

static void
bn_from_signed31 (bn256 *a, const sr256 *r)
{
  uint32_t r0, r1, r2, r3, r4, r5, r6, r7, r8;

  /* Input must be [0,modulus)... */
  r0 = r->v[0];
  r1 = r->v[1];
  r2 = r->v[2];
  r3 = r->v[3];
  r4 = r->v[4];
  r5 = r->v[5];
  r6 = r->v[6];
  r7 = r->v[7];
  r8 = r->v[8];

  a->word[0] = (r0 >>  0) | (r1 << 31);
  a->word[1] = (r1 >>  1) | (r2 << 30);
  a->word[2] = (r2 >>  2) | (r3 << 29);
  a->word[3] = (r3 >>  3) | (r4 << 28);
  a->word[4] = (r4 >>  4) | (r5 << 27);
  a->word[5] = (r5 >>  5) | (r6 << 26);
  a->word[6] = (r6 >>  6) | (r7 << 25);
  a->word[7] = (r7 >>  7) | (r8 << 24);
  /* ... then, (r8 >> 24) should be zero, here.  */
}

/**
 * @brief R = X^(-1) mod N
 *
 * Assume X and N are co-prime (or N is prime).
 * NOTE: If X==0, it return 0.
 *
 */
void
mod256_inv (bn256 *r, const bn256 *x, int is_25519)
{
  sr256 s[1];

  memcpy (r, x, sizeof (bn256));

  bn_to_signed31 (s, r);
  if (is_25519)
    modinv (s, &modulus_25519, modulus_inv31_25519, 19);
  else
    modinv (s, &modulus_secp256k1, modulus_inv31_secp256k1, 20);
  bn_from_signed31 (r, s);
}
