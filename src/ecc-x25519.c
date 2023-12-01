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
#include "mod.h"

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
 * (1) We use Radix-32 field arithmetic.  It's a representation like
 *     2^256-38, but it's more redundant.  For example, "1" can be
 *     represented in three ways in 256-bit: 1, 2^255-18, and
 *     2^256-37.
 *
 * (2) We use Montgomery double-and-add.
 *
 */

#ifndef BN256_C_IMPLEMENTATION
#define ASM_IMPLEMENTATION 1
#endif
/*
 *
 * 121665 = 0x1db41
 *            1 1101 1011 0100 0001
 */
static void
mod25638_mul_121665 (bn256 *x, const bn256 *a)
{
#if ASM_IMPLEMENTATION
#include "muladd_256.h"
  const uint32_t *s;
  uint32_t *d;
  uint32_t w;
  uint32_t c;

  s = a->word;
  d = x->word;
  memset (d, 0, sizeof (bn256));
  w = 121665;
  MULADD_256_ASM (s, d, w, c);
#else
  uint32_t c, c1;
  bn256 m[1];

  c = c1 = bn256_shift (m, a, 6); c += bn256_add (x, a, m);
  c1 <<= 2; c1 |= bn256_shift (m, m, 2); c = c + c1 + bn256_add (x, x, m);
  c1 <<= 1; c1 |= bn256_shift (m, m, 1); c = c + c1 + bn256_add (x, x, m);
  c1 <<= 2; c1 |= bn256_shift (m, m, 2); c = c + c1 + bn256_add (x, x, m);
  c1 <<= 1; c1 |= bn256_shift (m, m, 1); c = c + c1 + bn256_add (x, x, m);
  c1 <<= 2; c1 |= bn256_shift (m, m, 2); c = c + c1 + bn256_add (x, x, m);
  c1 <<= 1; c1 |= bn256_shift (m, m, 1); c = c + c1 + bn256_add (x, x, m);
  c1 <<= 1; c1 |= bn256_shift (m, m, 1); c = c + c1 + bn256_add (x, x, m);
#endif
  c = bn256_add_uint (x, x, c*38);
  x->word[0] += c * 38;
}


/* fe: Field Element */
typedef bn256 fe;
#define fe_add mod25638_add
#define fe_sub mod25638_sub
#define fe_mul mod25638_mul
#define fe_sqr mod25638_sqr
#define fe_m_d mod25638_mul_121665

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

#define tmp0 t0
#define tmp1 t1
#define tmp2 x1
#define tmp3 x0
#define tmp4 t0
#define tmp5 t1
#define tmp6 z0
#define tmp7 x1
#define tmp8 z1
#define tmp9 t0
#define tmpA t1
#define tmpB t0
#define tmpC t0
#define tmpD z0

                                    fe_add (tmp0,
                                              x1,
                                              z1);
                                            fe_sub (tmp1,
                                                      x1,
                                                      z1);
  fe_add (tmp2,
            x0,
            z0);
          fe_sub (tmp3,
                    x0,
                    z0);
                                    fe_mul (tmp4,
                                            tmp3,
                                            tmp0);
                                            fe_mul (tmp5,
                                                    tmp2,
                                                    tmp1);
  fe_sqr (tmp6,
          tmp2);
          fe_sqr (tmp7,
                  tmp3);
                                    fe_add (tmp8,
                                            tmp4,
                                            tmp5);
                                            fe_sub (tmp9,
                                                    tmp4,
                                                    tmp5);
  fe_mul (xp,
          tmp6,
          tmp7);
          fe_sub (tmpA,
                  tmp6,
                  tmp7);
                                    fe_sqr (xs,
                                            tmp8);
                                            fe_sqr (tmpB,
                                                    tmp9);
                                            fe_mul (zs,
                                                    tmpB, dif_x);
          fe_m_d (tmpC,
                  tmpA);
          fe_add (tmpD,
                  tmp6,
                  tmpC);
          fe_mul (zp,
                  tmpD,
                  tmpA);
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
  bn256 x0[1], z0[1], x1[1], z1[1];
  bn256 t0[1], t1[1];
  uint32_t swap = 0;
  const unsigned char *np = (const unsigned char *)n->word;

  /* P0 = O = (1:0)  */
  memset (x0, 0, sizeof (bn256));
  x0->word[0] = 1;
  memset (z0, 0, sizeof (bn256));

  /* P1 = (X:1) */
  memcpy (x1, q_x, sizeof (bn256));
  memcpy (z1, x0, sizeof (bn256));

  for (i = 254; i >= 0; i--)
    {
      uint32_t b = (np[i>>3]>>(i&7))&1;

      swap ^= b;
      bn256_swap_cond (x0, x1, swap);
      bn256_swap_cond (z0, z1, swap);
      swap = b;
      mont_d_and_a (x0, z0, x1, z1, q_x, t0, t1);
    }

  /* We know the LSB of N is always 0.  Thus, result is always in P0.  */
  /*
   * p0->z may be zero here, but our mod_inv doesn't raise error for 0,
   * but returns 0 (like the implementation of z^(p-2)), thus, RES will
   * be 0 in that case, which is correct value.
   */
  mod_inv (res, z0, p25519);
  mod25638_mul (res, res, x0);
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
