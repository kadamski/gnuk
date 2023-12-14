/*                                                    -*- coding: utf-8 -*-
 * ecc-x25519.c - Elliptic curve computation for
 *                the Montgomery curve: y^2 = x^3 + 486662*x^2 + x.
 *
 * Copyright (C) 2014, 2015, 2017, 2021, 2023
 *               Free Software Initiative of Japan
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

#include <stdint.h>
#include <string.h>
#include "bn.h"
#include "mod25638.h"
#include "modinv.h"

/*
 * References:
 *
 * [1] D. J. Bernstein. Curve25519: new Diffie-Hellman speed records.
 *     Proceedings of PKC 2006, to appear.
 *     http://cr.yp.to/papers.html#curve25519. Date: 2006.02.09.
 *
 * [2] D. J. Bernstein. Can we avoid tests for zero in fast
 *     elliptic-curve arithmetic?
 *     http://cr.yp.to/papers.html#curvezero. Date: 2006.07.26.
 *
 */

/*
 * IMPLEMENTATION NOTE
 *
 * (0) We assume that the processor has no cache, nor branch target
 *     prediction.  Thus, we don't avoid indexing by secret value.
 *     We don't avoid conditional jump if both cases have same timing,
 *     either.
 *
 * (1) We use the base of 2^25.5 (alternating 2^25 and 2^26).
 *
 * (2) We use Montgomery double-and-add.
 *
 */

/* Redundant representation with signed limb for bignum integer,
 * using 2^25.5 for the base.
 */
#define RR25519_WORDS 10
typedef struct rr25519 {
  int32_t w[RR25519_WORDS];
} rr25519;

/* X = 0 */
static inline void
rr25519_0 (rr25519 *x)
{
  memset(x, 0, sizeof (rr25519));
}

/* X = 1 */
static inline void
rr25519_1 (rr25519 *x)
{
  x->w[0] = 1;
  memset(&x->w[1], 0, sizeof (int32_t) * (RR25519_WORDS - 1));
}

/* DST = SRC */
static inline void
rr25519_copy (rr25519 *dst, const rr25519 *src)
{
  memcpy (dst, src, sizeof (rr25519));
}

/* A <=> B conditionally */
static void
rr25519_swap_cond (rr25519 *a, rr25519 *b, uint32_t c)
{
  int i;
  uint32_t mask = 0UL - c;
  uint32_t *p = (uint32_t *)a->w;
  uint32_t *q = (uint32_t *)b->w;

  asm volatile ("" : "+r" (mask) : : "memory");
  for (i = 0; i < RR25519_WORDS; i++)
    {
      uint32_t t = mask & (*p^*q);
      *p++ ^= t;
      *q++ ^= t;
    }
}

/* X = (A + B) mod 2^255-19 */
static void
rr25519_add (rr25519 *x, const rr25519 *a, const rr25519 *b)
{
  x->w[0] = a->w[0] + b->w[0];
  x->w[1] = a->w[1] + b->w[1];
  x->w[2] = a->w[2] + b->w[2];
  x->w[3] = a->w[3] + b->w[3];
  x->w[4] = a->w[4] + b->w[4];
  x->w[5] = a->w[5] + b->w[5];
  x->w[6] = a->w[6] + b->w[6];
  x->w[7] = a->w[7] + b->w[7];
  x->w[8] = a->w[8] + b->w[8];
  x->w[9] = a->w[9] + b->w[9];
}

/* X = (A - B) mod 2^255-19 */
static void
rr25519_sub (rr25519 *x, const rr25519 *a, const rr25519 *b)
{
  x->w[0] = a->w[0] - b->w[0];
  x->w[1] = a->w[1] - b->w[1];
  x->w[2] = a->w[2] - b->w[2];
  x->w[3] = a->w[3] - b->w[3];
  x->w[4] = a->w[4] - b->w[4];
  x->w[5] = a->w[5] - b->w[5];
  x->w[6] = a->w[6] - b->w[6];
  x->w[7] = a->w[7] - b->w[7];
  x->w[8] = a->w[8] - b->w[8];
  x->w[9] = a->w[9] - b->w[9];
}

/* Multiply two 32-bit integers, resulting 64-bit integer.  */
static inline int64_t
m32x32 (int32_t a, int32_t b)
{
  return a * (int64_t)b;
}

/* X = (A * B) mod 2^255-19 */
static void
rr25519_mul (rr25519 *x, const rr25519 *a, const rr25519 *b)
{
  int64_t carry0, carry1, carry2, carry3, carry4;
  int64_t carry5, carry6, carry7, carry8, carry9;

  int32_t a0 = a->w[0];
  int32_t a1 = a->w[1];
  int32_t a2 = a->w[2];
  int32_t a3 = a->w[3];
  int32_t a4 = a->w[4];
  int32_t a5 = a->w[5];
  int32_t a6 = a->w[6];
  int32_t a7 = a->w[7];
  int32_t a8 = a->w[8];
  int32_t a9 = a->w[9];

  int32_t b0 = b->w[0];
  int32_t b1 = b->w[1];
  int32_t b2 = b->w[2];
  int32_t b3 = b->w[3];
  int32_t b4 = b->w[4];
  int32_t b5 = b->w[5];
  int32_t b6 = b->w[6];
  int32_t b7 = b->w[7];
  int32_t b8 = b->w[8];
  int32_t b9 = b->w[9];

  int32_t b1_19 = 19 * b1;
  int32_t b2_19 = 19 * b2;
  int32_t b3_19 = 19 * b3;
  int32_t b4_19 = 19 * b4;
  int32_t b5_19 = 19 * b5;
  int32_t b6_19 = 19 * b6;
  int32_t b7_19 = 19 * b7;
  int32_t b8_19 = 19 * b8;
  int32_t b9_19 = 19 * b9;
  int32_t a1_2  = 2 * a1;
  int32_t a3_2  = 2 * a3;
  int32_t a5_2  = 2 * a5;
  int32_t a7_2  = 2 * a7;
  int32_t a9_2  = 2 * a9;

  int64_t a0b0    = m32x32 (a0, b0);
  int64_t a0b1    = m32x32 (a0, b1);
  int64_t a0b2    = m32x32 (a0, b2);
  int64_t a0b3    = m32x32 (a0, b3);
  int64_t a0b4    = m32x32 (a0, b4);
  int64_t a0b5    = m32x32 (a0, b5);
  int64_t a0b6    = m32x32 (a0, b6);
  int64_t a0b7    = m32x32 (a0, b7);
  int64_t a0b8    = m32x32 (a0, b8);
  int64_t a0b9    = m32x32 (a0, b9);
  int64_t a1b0    = m32x32 (a1, b0);
  int64_t a1b1_2  = m32x32 (a1_2, b1);
  int64_t a1b2    = m32x32 (a1, b2);
  int64_t a1b3_2  = m32x32 (a1_2, b3);
  int64_t a1b4    = m32x32 (a1, b4);
  int64_t a1b5_2  = m32x32 (a1_2, b5);
  int64_t a1b6    = m32x32 (a1, b6);
  int64_t a1b7_2  = m32x32 (a1_2, b7);
  int64_t a1b8    = m32x32 (a1, b8);
  int64_t a1b9_38 = m32x32 (a1_2, b9_19);
  int64_t a2b0    = m32x32 (a2, b0);
  int64_t a2b1    = m32x32 (a2, b1);
  int64_t a2b2    = m32x32 (a2, b2);
  int64_t a2b3    = m32x32 (a2, b3);
  int64_t a2b4    = m32x32 (a2, b4);
  int64_t a2b5    = m32x32 (a2, b5);
  int64_t a2b6    = m32x32 (a2, b6);
  int64_t a2b7    = m32x32 (a2, b7);
  int64_t a2b8_19 = m32x32 (a2, b8_19);
  int64_t a2b9_19 = m32x32 (a2, b9_19);
  int64_t a3b0    = m32x32 (a3, b0);
  int64_t a3b1_2  = m32x32 (a3_2, b1);
  int64_t a3b2    = m32x32 (a3, b2);
  int64_t a3b3_2  = m32x32 (a3_2, b3);
  int64_t a3b4    = m32x32 (a3, b4);
  int64_t a3b5_2  = m32x32 (a3_2, b5);
  int64_t a3b6    = m32x32 (a3, b6);
  int64_t a3b7_38 = m32x32 (a3_2, b7_19);
  int64_t a3b8_19 = m32x32 (a3, b8_19);
  int64_t a3b9_38 = m32x32 (a3_2, b9_19);
  int64_t a4b0    = m32x32 (a4, b0);
  int64_t a4b1    = m32x32 (a4, b1);
  int64_t a4b2    = m32x32 (a4, b2);
  int64_t a4b3    = m32x32 (a4, b3);
  int64_t a4b4    = m32x32 (a4, b4);
  int64_t a4b5    = m32x32 (a4, b5);
  int64_t a4b6_19 = m32x32 (a4, b6_19);
  int64_t a4b7_19 = m32x32 (a4, b7_19);
  int64_t a4b8_19 = m32x32 (a4, b8_19);
  int64_t a4b9_19 = m32x32 (a4, b9_19);
  int64_t a5b0    = m32x32 (a5, b0);
  int64_t a5b1_2  = m32x32 (a5_2, b1);
  int64_t a5b2    = m32x32 (a5, b2);
  int64_t a5b3_2  = m32x32 (a5_2, b3);
  int64_t a5b4    = m32x32 (a5, b4);
  int64_t a5b5_38 = m32x32 (a5_2, b5_19);
  int64_t a5b6_19 = m32x32 (a5, b6_19);
  int64_t a5b7_38 = m32x32 (a5_2, b7_19);
  int64_t a5b8_19 = m32x32 (a5, b8_19);
  int64_t a5b9_38 = m32x32 (a5_2, b9_19);
  int64_t a6b0    = m32x32 (a6, b0);
  int64_t a6b1    = m32x32 (a6, b1);
  int64_t a6b2    = m32x32 (a6, b2);
  int64_t a6b3    = m32x32 (a6, b3);
  int64_t a6b4_19 = m32x32 (a6, b4_19);
  int64_t a6b5_19 = m32x32 (a6, b5_19);
  int64_t a6b6_19 = m32x32 (a6, b6_19);
  int64_t a6b7_19 = m32x32 (a6, b7_19);
  int64_t a6b8_19 = m32x32 (a6, b8_19);
  int64_t a6b9_19 = m32x32 (a6, b9_19);
  int64_t a7b0    = m32x32 (a7, b0);
  int64_t a7b1_2  = m32x32 (a7_2, b1);
  int64_t a7b2    = m32x32 (a7, b2);
  int64_t a7b3_38 = m32x32 (a7_2, b3_19);
  int64_t a7b4_19 = m32x32 (a7, b4_19);
  int64_t a7b5_38 = m32x32 (a7_2, b5_19);
  int64_t a7b6_19 = m32x32 (a7, b6_19);
  int64_t a7b7_38 = m32x32 (a7_2, b7_19);
  int64_t a7b8_19 = m32x32 (a7, b8_19);
  int64_t a7b9_38 = m32x32 (a7_2, b9_19);
  int64_t a8b0    = m32x32 (a8, b0);
  int64_t a8b1    = m32x32 (a8, b1);
  int64_t a8b2_19 = m32x32 (a8, b2_19);
  int64_t a8b3_19 = m32x32 (a8, b3_19);
  int64_t a8b4_19 = m32x32 (a8, b4_19);
  int64_t a8b5_19 = m32x32 (a8, b5_19);
  int64_t a8b6_19 = m32x32 (a8, b6_19);
  int64_t a8b7_19 = m32x32 (a8, b7_19);
  int64_t a8b8_19 = m32x32 (a8, b8_19);
  int64_t a8b9_19 = m32x32 (a8, b9_19);
  int64_t a9b0    = m32x32 (a9, b0);
  int64_t a9b1_38 = m32x32 (a9_2, b1_19);
  int64_t a9b2_19 = m32x32 (a9, b2_19);
  int64_t a9b3_38 = m32x32 (a9_2, b3_19);
  int64_t a9b4_19 = m32x32 (a9, b4_19);
  int64_t a9b5_38 = m32x32 (a9_2, b5_19);
  int64_t a9b6_19 = m32x32 (a9, b6_19);
  int64_t a9b7_38 = m32x32 (a9_2, b7_19);
  int64_t a9b8_19 = m32x32 (a9, b8_19);
  int64_t a9b9_38 = m32x32 (a9_2, b9_19);

  int64_t x0 = (a0b0 + a1b9_38 + a2b8_19 + a3b7_38 + a4b6_19 + a5b5_38
                + a6b4_19 + a7b3_38 + a8b2_19 + a9b1_38);
  int64_t x1 = (a0b1 + a1b0 + a2b9_19 + a3b8_19 + a4b7_19 + a5b6_19 + a6b5_19
                + a7b4_19 + a8b3_19 + a9b2_19);
  int64_t x2 = (a0b2 + a1b1_2 + a2b0 + a3b9_38 + a4b8_19 + a5b7_38 + a6b6_19
                + a7b5_38 + a8b4_19 + a9b3_38);
  int64_t x3 = (a0b3 + a1b2 + a2b1 + a3b0 + a4b9_19 + a5b8_19 + a6b7_19
                + a7b6_19 + a8b5_19 + a9b4_19);
  int64_t x4 = (a0b4 + a1b3_2 + a2b2 + a3b1_2 + a4b0 + a5b9_38 + a6b8_19
                + a7b7_38 + a8b6_19 + a9b5_38);
  int64_t x5 = (a0b5 + a1b4 + a2b3 + a3b2 + a4b1 + a5b0 + a6b9_19 + a7b8_19
                + a8b7_19 + a9b6_19);
  int64_t x6 = (a0b6 + a1b5_2 + a2b4 + a3b3_2 + a4b2 + a5b1_2 + a6b0
                + a7b9_38 + a8b8_19 + a9b7_38);
  int64_t x7 = (a0b7 + a1b6 + a2b5 + a3b4 + a4b3 + a5b2 + a6b1 + a7b0
                + a8b9_19 + a9b8_19);
  int64_t x8 = (a0b8 + a1b7_2 + a2b6 + a3b5_2 + a4b4 + a5b3_2 + a6b2 + a7b1_2
                + a8b0 + a9b9_38);
  int64_t x9 = (a0b9 + a1b8 + a2b7 + a3b6 + a4b5 + a5b4 + a6b3 + a7b2
                + a8b1 + a9b0);

  carry0 = (x0 + (1 << 25)) >> 26;
  x1 += carry0;
  x0 -= (carry0 << 26);
  carry4 = (x4 + (1 << 25)) >> 26;
  x5 += carry4;
  x4 -= (carry4 << 26);

  carry1 = (x1 + (1 << 24)) >> 25;
  x2 += carry1;
  x1 -= (carry1 << 25);
  carry5 = (x5 + (1 << 24)) >> 25;
  x6 += carry5;
  x5 -= (carry5 << 25);

  carry2 = (x2 + (1 << 25)) >> 26;
  x3 += carry2;
  x2 -= (carry2 << 26);
  carry6 = (x6 + (1 << 25)) >> 26;
  x7 += carry6;
  x6 -= (carry6 << 26);

  carry3 = (x3 + (1 << 24)) >> 25;
  x4 += carry3;
  x3 -= (carry3 << 25);
  carry7 = (x7 + (1 << 24)) >> 25;
  x8 += carry7;
  x7 -= (carry7 << 25);

  carry4 = (x4 + (1 << 25)) >> 26;
  x5 += carry4;
  x4 -= (carry4 << 26);
  carry8 = (x8 + (1 << 25)) >> 26;
  x9 += carry8;
  x8 -= (carry8 << 26);

  carry9 = (x9 + (1 << 24)) >> 25;
  x0 += carry9 * 19;
  x9 -= (carry9 << 25);

  carry0 = (x0 + (1 << 25)) >> 26;
  x1 += carry0;
  x0 -= (carry0 << 26);

  x->w[0] = (int32_t)x0;
  x->w[1] = (int32_t)x1;
  x->w[2] = (int32_t)x2;
  x->w[3] = (int32_t)x3;
  x->w[4] = (int32_t)x4;
  x->w[5] = (int32_t)x5;
  x->w[6] = (int32_t)x6;
  x->w[7] = (int32_t)x7;
  x->w[8] = (int32_t)x8;
  x->w[9] = (int32_t)x9;
}

/* X = (A ^ 2) mod 2^255-19 */
static void
rr25519_sqr (rr25519 *x, const rr25519 *a)
{
  int64_t carry0, carry1, carry2, carry3, carry4;
  int64_t carry5, carry6, carry7, carry8, carry9;

  int32_t a0 = a->w[0];
  int32_t a1 = a->w[1];
  int32_t a2 = a->w[2];
  int32_t a3 = a->w[3];
  int32_t a4 = a->w[4];
  int32_t a5 = a->w[5];
  int32_t a6 = a->w[6];
  int32_t a7 = a->w[7];
  int32_t a8 = a->w[8];
  int32_t a9 = a->w[9];

  int32_t a0_2  = 2 * a0;
  int32_t a1_2  = 2 * a1;
  int32_t a2_2  = 2 * a2;
  int32_t a3_2  = 2 * a3;
  int32_t a4_2  = 2 * a4;
  int32_t a5_2  = 2 * a5;
  int32_t a6_2  = 2 * a6;
  int32_t a7_2  = 2 * a7;
  int32_t a5_38 = 38 * a5;
  int32_t a6_19 = 19 * a6;
  int32_t a7_38 = 38 * a7;
  int32_t a8_19 = 19 * a8;
  int32_t a9_38 = 38 * a9;

  int64_t a0a0    = m32x32 (a0, a0);
  int64_t a0a1_2  = m32x32 (a0_2, a1);
  int64_t a0a2_2  = m32x32 (a0_2, a2);
  int64_t a0a3_2  = m32x32 (a0_2, a3);
  int64_t a0a4_2  = m32x32 (a0_2, a4);
  int64_t a0a5_2  = m32x32 (a0_2, a5);
  int64_t a0a6_2  = m32x32 (a0_2, a6);
  int64_t a0a7_2  = m32x32 (a0_2, a7);
  int64_t a0a8_2  = m32x32 (a0_2, a8);
  int64_t a0a9_2  = m32x32 (a0_2, a9);
  int64_t a1a1_2  = m32x32 (a1_2, a1);
  int64_t a1a2_2  = m32x32 (a1_2, a2);
  int64_t a1a3_4  = m32x32 (a1_2, a3_2);
  int64_t a1a4_2  = m32x32 (a1_2, a4);
  int64_t a1a5_4  = m32x32 (a1_2, a5_2);
  int64_t a1a6_2  = m32x32 (a1_2, a6);
  int64_t a1a7_4  = m32x32 (a1_2, a7_2);
  int64_t a1a8_2  = m32x32 (a1_2, a8);
  int64_t a1a9_76 = m32x32 (a1_2, a9_38);
  int64_t a2a2    = m32x32 (a2, a2);
  int64_t a2a3_2  = m32x32 (a2_2, a3);
  int64_t a2a4_2  = m32x32 (a2_2, a4);
  int64_t a2a5_2  = m32x32 (a2_2, a5);
  int64_t a2a6_2  = m32x32 (a2_2, a6);
  int64_t a2a7_2  = m32x32 (a2_2, a7);
  int64_t a2a8_38 = m32x32 (a2_2, a8_19);
  int64_t a2a9_38 = m32x32 (a2, a9_38);
  int64_t a3a3_2  = m32x32 (a3_2, a3);
  int64_t a3a4_2  = m32x32 (a3_2, a4);
  int64_t a3a5_4  = m32x32 (a3_2, a5_2);
  int64_t a3a6_2  = m32x32 (a3_2, a6);
  int64_t a3a7_76 = m32x32 (a3_2, a7_38);
  int64_t a3a8_38 = m32x32 (a3_2, a8_19);
  int64_t a3a9_76 = m32x32 (a3_2, a9_38);
  int64_t a4a4    = m32x32 (a4, a4);
  int64_t a4a5_2  = m32x32 (a4_2, a5);
  int64_t a4a6_38 = m32x32 (a4_2, a6_19);
  int64_t a4a7_38 = m32x32 (a4, a7_38);
  int64_t a4a8_38 = m32x32 (a4_2, a8_19);
  int64_t a4a9_38 = m32x32 (a4, a9_38);
  int64_t a5a5_38 = m32x32 (a5, a5_38);
  int64_t a5a6_38 = m32x32 (a5_2, a6_19);
  int64_t a5a7_76 = m32x32 (a5_2, a7_38);
  int64_t a5a8_38 = m32x32 (a5_2, a8_19);
  int64_t a5a9_76 = m32x32 (a5_2, a9_38);
  int64_t a6a6_19 = m32x32 (a6, a6_19);
  int64_t a6a7_38 = m32x32 (a6, a7_38);
  int64_t a6a8_38 = m32x32 (a6_2, a8_19);
  int64_t a6a9_38 = m32x32 (a6, a9_38);
  int64_t a7a7_38 = m32x32 (a7, a7_38);
  int64_t a7a8_38 = m32x32 (a7_2, a8_19);
  int64_t a7a9_76 = m32x32 (a7_2, a9_38);
  int64_t a8a8_19 = m32x32 (a8, a8_19);
  int64_t a8a9_38 = m32x32 (a8, a9_38);
  int64_t a9a9_38 = m32x32 (a9, a9_38);

  int64_t x0 = a0a0 + a1a9_76 + a2a8_38 + a3a7_76 + a4a6_38 + a5a5_38;
  int64_t x1 = a0a1_2 + a2a9_38 + a3a8_38 + a4a7_38 + a5a6_38;
  int64_t x2 = a0a2_2 + a1a1_2 + a3a9_76 + a4a8_38 + a5a7_76 + a6a6_19;
  int64_t x3 = a0a3_2 + a1a2_2 + a4a9_38 + a5a8_38 + a6a7_38;
  int64_t x4 = a0a4_2 + a1a3_4 + a2a2 + a5a9_76 + a6a8_38 + a7a7_38;
  int64_t x5 = a0a5_2 + a1a4_2 + a2a3_2 + a6a9_38 + a7a8_38;
  int64_t x6 = a0a6_2 + a1a5_4 + a2a4_2 + a3a3_2 + a7a9_76 + a8a8_19;
  int64_t x7 = a0a7_2 + a1a6_2 + a2a5_2 + a3a4_2 + a8a9_38;
  int64_t x8 = a0a8_2 + a1a7_4 + a2a6_2 + a3a5_4 + a4a4 + a9a9_38;
  int64_t x9 = a0a9_2 + a1a8_2 + a2a7_2 + a3a6_2 + a4a5_2;

  carry0 = (x0 + (1 << 25)) >> 26;
  x1 += carry0;
  x0 -= (carry0 << 26);
  carry4 = (x4 + (1 << 25)) >> 26;
  x5 += carry4;
  x4 -= (carry4 << 26);

  carry1 = (x1 + (1 << 24)) >> 25;
  x2 += carry1;
  x1 -= (carry1 << 25);
  carry5 = (x5 + (1 << 24)) >> 25;
  x6 += carry5;
  x5 -= (carry5 << 25);

  carry2 = (x2 + (1 << 25)) >> 26;
  x3 += carry2;
  x2 -= (carry2 << 26);
  carry6 = (x6 + (1 << 25)) >> 26;
  x7 += carry6;
  x6 -= (carry6 << 26);

  carry3 = (x3 + (1 << 24)) >> 25;
  x4 += carry3;
  x3 -= (carry3 << 25);
  carry7 = (x7 + (1 << 24)) >> 25;
  x8 += carry7;
  x7 -= (carry7 << 25);

  carry4 = (x4 + (1 << 25)) >> 26;
  x5 += carry4;
  x4 -= (carry4 << 26);
  carry8 = (x8 + (1 << 25)) >> 26;
  x9 += carry8;
  x8 -= (carry8 << 26);

  carry9 = (x9 + (1 << 24)) >> 25;
  x0 += carry9 * 19;
  x9 -= (carry9 << 25);

  carry0 = (x0 + (1 << 25)) >> 26;
  x1 += carry0;
  x0 -= (carry0 << 26);

  x->w[0] = (int32_t)x0;
  x->w[1] = (int32_t)x1;
  x->w[2] = (int32_t)x2;
  x->w[3] = (int32_t)x3;
  x->w[4] = (int32_t)x4;
  x->w[5] = (int32_t)x5;
  x->w[6] = (int32_t)x6;
  x->w[7] = (int32_t)x7;
  x->w[8] = (int32_t)x8;
  x->w[9] = (int32_t)x9;
}

/*
 * A = 486662
 * a24 which stands for (A - 2)/4 = 121665
 */
static void
rr25519_mul_121665 (rr25519 *x, const rr25519 *a)
{
  int64_t carry0, carry1, carry2, carry3, carry4;
  int64_t carry5, carry6, carry7, carry8, carry9;
  int64_t v0 = m32x32 (a->w[0], 121665);
  int64_t v1 = m32x32 (a->w[1], 121665);
  int64_t v2 = m32x32 (a->w[2], 121665);
  int64_t v3 = m32x32 (a->w[3], 121665);
  int64_t v4 = m32x32 (a->w[4], 121665);
  int64_t v5 = m32x32 (a->w[5], 121665);
  int64_t v6 = m32x32 (a->w[6], 121665);
  int64_t v7 = m32x32 (a->w[7], 121665);
  int64_t v8 = m32x32 (a->w[8], 121665);
  int64_t v9 = m32x32 (a->w[9], 121665);

  carry1 = (v1 + (1 << 24)) >> 25;
  v2 += carry1;
  v1 -= (carry1 << 25);
  carry3 = (v3 + (1 << 24)) >> 25;
  v4 += carry3;
  v3 -= (carry3 << 25);
  carry5 = (v5 + (1 << 24)) >> 25;
  v6 += carry5;
  v5 -= (carry5 << 25);
  carry7 = (v7 + (1 << 24)) >> 25;
  v8 += carry7;
  v7 -= (carry7 << 25);
  carry9 = (v9 + (1 << 24)) >> 25;
  v0 += carry9 * 19;
  v9 -= (carry9 << 25);

  carry0 = (v0 + (1 << 25)) >> 26;
  v1 += carry0;
  v0 -= (carry0 << 26);
  carry2 = (v2 + (1 << 25)) >> 26;
  v3 += carry2;
  v2 -= (carry2 << 26);
  carry4 = (v4 + (1 << 25)) >> 26;
  v5 += carry4;
  v4 -= (carry4 << 26);
  carry6 = (v6 + (1 << 25)) >> 26;
  v7 += carry6;
  v6 -= (carry6 << 26);
  carry8 = (v8 + (1 << 25)) >> 26;
  v9 += carry8;
  v8 -= (carry8 << 26);

  x->w[0] = (int32_t)v0;
  x->w[1] = (int32_t)v1;
  x->w[2] = (int32_t)v2;
  x->w[3] = (int32_t)v3;
  x->w[4] = (int32_t)v4;
  x->w[5] = (int32_t)v5;
  x->w[6] = (int32_t)v6;
  x->w[7] = (int32_t)v7;
  x->w[8] = (int32_t)v8;
  x->w[9] = (int32_t)v9;
}

/* Copied from aes.c, changing the return type into 64-bit. */
static uint64_t
get_uint32_le (const unsigned char *b, unsigned int i)
{
  return (  ((uint64_t)b[i    ]      )
          | ((uint64_t)b[i + 1] <<  8)
          | ((uint64_t)b[i + 2] << 16)
          | ((uint64_t)b[i + 3] << 24));
}

static uint64_t
get_uint24_le (const unsigned char *b, unsigned int i)
{
  return (  ((uint64_t)b[i    ]      )
          | ((uint64_t)b[i + 1] <<  8)
          | ((uint64_t)b[i + 2] << 16));
}

/* Expand byte representation into the redundant representation.  */
static void
rr25519_expand (rr25519 *x, const unsigned char *src)
{
  int64_t carry0, carry1, carry2, carry3, carry4;
  int64_t carry5, carry6, carry7, carry8, carry9;
  int64_t v0 = get_uint32_le (src, 0);
  int64_t v1 = get_uint24_le (src, 4) << 6;
  int64_t v2 = get_uint24_le (src, 7) << 5;
  int64_t v3 = get_uint24_le (src, 10) << 3;
  int64_t v4 = get_uint24_le (src, 13) << 2;
  int64_t v5 = get_uint32_le (src, 16);
  int64_t v6 = get_uint24_le (src, 20) << 7;
  int64_t v7 = get_uint24_le (src, 23) << 5;
  int64_t v8 = get_uint24_le (src, 26) << 4;
  int64_t v9 = (get_uint24_le (src, 29) & 0x7fffff) << 2;

  carry1 = (v1 + (1 << 24)) >> 25;
  v2 += carry1;
  v1 -= (carry1 << 25);
  carry3 = (v3 + (1 << 24)) >> 25;
  v4 += carry3;
  v3 -= (carry3 << 25);
  carry5 = (v5 + (1 << 24)) >> 25;
  v6 += carry5;
  v5 -= (carry5 << 25);
  carry7 = (v7 + (1 << 24)) >> 25;
  v8 += carry7;
  v7 -= (carry7 << 25);
  carry9 = (v9 + (1 << 24)) >> 25;
  v0 += carry9 * 19;
  v9 -= (carry9 << 25);

  carry0 = (v0 + (1 << 25)) >> 26;
  v1 += carry0;
  v0 -= (carry0 << 26);
  carry2 = (v2 + (1 << 25)) >> 26;
  v3 += carry2;
  v2 -= (carry2 << 26);
  carry4 = (v4 + (1 << 25)) >> 26;
  v5 += carry4;
  v4 -= (carry4 << 26);
  carry6 = (v6 + (1 << 25)) >> 26;
  v7 += carry6;
  v6 -= (carry6 << 26);
  carry8 = (v8 + (1 << 25)) >> 26;
  v9 += carry8;
  v8 -= (carry8 << 26);

  x->w[0] = (int32_t)v0;
  x->w[1] = (int32_t)v1;
  x->w[2] = (int32_t)v2;
  x->w[3] = (int32_t)v3;
  x->w[4] = (int32_t)v4;
  x->w[5] = (int32_t)v5;
  x->w[6] = (int32_t)v6;
  x->w[7] = (int32_t)v7;
  x->w[8] = (int32_t)v8;
  x->w[9] = (int32_t)v9;
}

/* Strong reduce */
static void
rr25519_reduce (rr25519 *x, const rr25519 *a)
{
  int32_t q;
  int32_t carry0, carry1, carry2, carry3, carry4;
  int32_t carry5, carry6, carry7, carry8, carry9;
  int32_t x0 = a->w[0];
  int32_t x1 = a->w[1];
  int32_t x2 = a->w[2];
  int32_t x3 = a->w[3];
  int32_t x4 = a->w[4];
  int32_t x5 = a->w[5];
  int32_t x6 = a->w[6];
  int32_t x7 = a->w[7];
  int32_t x8 = a->w[8];
  int32_t x9 = a->w[9];

  q = (19 * x9 + (1 << 24)) >> 25;
  q = (x0 + q) >> 26;
  q = (x1 + q) >> 25;
  q = (x2 + q) >> 26;
  q = (x3 + q) >> 25;
  q = (x4 + q) >> 26;
  q = (x5 + q) >> 25;
  q = (x6 + q) >> 26;
  q = (x7 + q) >> 25;
  q = (x8 + q) >> 26;
  q = (x9 + q) >> 25;

  x0 += 19 * q;

  carry0 = x0 >> 26;
  x1 += carry0;
  x0 -= (carry0 << 26);
  carry1 = x1 >> 25;
  x2 += carry1;
  x1 -= (carry1 << 25);
  carry2 = x2 >> 26;
  x3 += carry2;
  x2 -= (carry2 << 26);
  carry3 = x3 >> 25;
  x4 += carry3;
  x3 -= (carry3 << 25);
  carry4 = x4 >> 26;
  x5 += carry4;
  x4 -= (carry4 << 26);
  carry5 = x5 >> 25;
  x6 += carry5;
  x5 -= (carry5 << 25);
  carry6 = x6 >> 26;
  x7 += carry6;
  x6 -= (carry6 << 26);
  carry7 = x7 >> 25;
  x8 += carry7;
  x7 -= (carry7 << 25);
  carry8 = x8 >> 26;
  x9 += carry8;
  x8 -= (carry8 << 26);
  carry9 = x9 >> 25;
  x9 -= (carry9 << 25);

  x->w[0] = x0;
  x->w[1] = x1;
  x->w[2] = x2;
  x->w[3] = x3;
  x->w[4] = x4;
  x->w[5] = x5;
  x->w[6] = x6;
  x->w[7] = x7;
  x->w[8] = x8;
  x->w[9] = x9;
}

static void
rr25519_contract (unsigned char *dst, const rr25519 *x)
{
  rr25519 t[1];

  rr25519_reduce (t, x);
  dst[0]  = t->w[0] >> 0;
  dst[1]  = t->w[0] >> 8;
  dst[2]  = t->w[0] >> 16;
  dst[3]  = (t->w[0] >> 24) | (t->w[1] << 2);
  dst[4]  = t->w[1] >> 6;
  dst[5]  = t->w[1] >> 14;
  dst[6]  = (t->w[1] >> 22) | (t->w[2] << 3);
  dst[7]  = t->w[2] >> 5;
  dst[8]  = t->w[2] >> 13;
  dst[9]  = (t->w[2] >> 21) | (t->w[3] << 5);
  dst[10] = t->w[3] >> 3;
  dst[11] = t->w[3] >> 11;
  dst[12] = (t->w[3] >> 19) | (t->w[4] << 6);
  dst[13] = t->w[4] >> 2;
  dst[14] = t->w[4] >> 10;
  dst[15] = t->w[4] >> 18;
  dst[16] = t->w[5] >> 0;
  dst[17] = t->w[5] >> 8;
  dst[18] = t->w[5] >> 16;
  dst[19] = (t->w[5] >> 24) | (t->w[6] << 1);
  dst[20] = t->w[6] >> 7;
  dst[21] = t->w[6] >> 15;
  dst[22] = (t->w[6] >> 23) | (t->w[7] << 3);
  dst[23] = t->w[7] >> 5;
  dst[24] = t->w[7] >> 13;
  dst[25] = (t->w[7] >> 21) | (t->w[8] << 4);
  dst[26] = t->w[8] >> 4;
  dst[27] = t->w[8] >> 12;
  dst[28] = (t->w[8] >> 20) | (t->w[9] << 6);
  dst[29] = t->w[9] >> 2;
  dst[30] = t->w[9] >> 10;
  dst[31] = t->w[9] >> 18;
}

/* fe: Field Element */
typedef rr25519 fe;
#define fe_add       rr25519_add
#define fe_sub       rr25519_sub
#define fe_mul       rr25519_mul
#define fe_sqr       rr25519_sqr
#define fe_a24       rr25519_mul_121665
#define fe_swap_cond rr25519_swap_cond
#define fe_0         rr25519_0
#define fe_1         rr25519_1
#define fe_copy      rr25519_copy
#define fe_expand    rr25519_expand
#define fe_contract  rr25519_contract

/**
 * @brief  Process Montgomery double-and-add
 *
 * With Q0, Q1, DIF (= Q0 - Q1), compute PRD = 2Q0, SUM = Q0 + Q1
 * On return, PRD is in Q0, SUM is in Q1
 * Caller provides temporary T0 and T1
 *
 * Note: indentation graphycally expresses the ladder.
 */
static void
mont_d_and_a (fe *x0, fe *z0, fe *x1, fe *z1, const fe *dif_x, fe *t0, fe *t1)
{
#define xp   x0
#define zp   z0
#define xs   x1
#define zs   z1
#define C       t0
#define D       t1
#define A       x1
#define B       x0
#define CB      t0
#define DA      t1
#define AA      z0
#define BB      x1
#define CBpDA   z1              /* CB + DA */
#define CBmDA   t0              /* CB - DA */
#define E       t1
#define CBmDAsq t0              /* (CB - DA)^2 */
#define a24E    t0
#define a24EpAA z0              /* AA + a24E */

                                    fe_add (C, x1, z1);
                                            fe_sub (D, x1, z1);
  fe_add (A, x0, z0);
          fe_sub (B, x0, z0);
                                    fe_mul (CB, B, C);
                                            fe_mul (DA, A, D);
  fe_sqr (AA, A);
          fe_sqr (BB, B);
                                    fe_add (CBpDA, CB, DA);
                                            fe_sub (CBmDA, CB, DA);
  fe_mul (xp, AA, BB);
          fe_sub (E, AA, BB);
                                    fe_sqr (xs, CBpDA);
                                            fe_sqr (CBmDAsq, CBmDA);
                                            fe_mul (zs, CBmDAsq, dif_x);
          fe_a24 (a24E, E);
          fe_add (a24EpAA, AA, a24E);
          fe_mul (zp, a24EpAA, E);
}


/**
 * @brief	RES  = x-coordinate of [n]Q
 *
 * @param N	Scalar N (three least significant bits are 000)
 * @param Q_X	x-coordinate of Q
 *
 */
static void
compute_nQ (bn256 *res, const bn256 *n, const bn256 *q_x)
{
  int i;
  fe x0[1], z0[1], x1[1], z1[1];
  fe t0[1], t1[1], q_x_rr[1];
  bn256 x0bn[1], z0bn[1];
  uint32_t swap = 0;
  const unsigned char *np = (const unsigned char *)n->word;

  /* P0 = O = (1:0)  */
  fe_1 (x0);
  fe_0 (z0);

  /* P1 = (X:1) */
  fe_expand (x1, (const unsigned char *)q_x);
  fe_copy (q_x_rr, x1);
  fe_copy (z1, x0);

  for (i = 254; i >= 0; i--)
    {
      uint32_t b = (np[i>>3]>>(i&7))&1;

      swap ^= b;
      fe_swap_cond (x0, x1, swap);
      fe_swap_cond (z0, z1, swap);
      swap = b;
      mont_d_and_a (x0, z0, x1, z1, q_x_rr, t0, t1);
    }

  /* We know the LSB of N is always 0.  Thus, result is always in P0.  */
  /*
   * p0->z may be zero here, but our mod_inv doesn't raise error for 0,
   * but returns 0 (like the implementation of z^(p-2)), thus, RES will
   * be 0 in that case, which is correct value.
   */
  fe_contract ((unsigned char *)x0bn, x0);
  fe_contract ((unsigned char *)z0bn, z0);
  mod256_inv (res, z0bn, 1);
  mod25638_mul (res, res, x0bn);
  mod25519_reduce (res);
}


void
ecdh_compute_public_25519 (const uint8_t *key_data, uint8_t *pubkey)
{
  bn256 gx[1];
  bn256 k[1];
  bn256 pk[1];

  memset (gx, 0, sizeof (bn256));
  gx[0].word[0] = 9;			/* Gx = 9 */
  memcpy (k, key_data, sizeof (bn256));

  compute_nQ (pk, k, gx);
  memcpy (pubkey, pk, sizeof (bn256));
}

int
ecdh_decrypt_curve25519 (const uint8_t *input, uint8_t *output,
			 const uint8_t *key_data)
{
  bn256 q_x[1];
  bn256 k[1];
  bn256 shared[1];

  memcpy (q_x, input, sizeof (bn256));
  memcpy (k, key_data, sizeof (bn256));
  compute_nQ (shared, k, q_x);
  memcpy (output, shared, sizeof (bn256));
  return 0;
}
