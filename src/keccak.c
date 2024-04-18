/*
 * keccak.c -- Compute Keccak hash.
 *
 * Copyright (C) 2021, 2024  Free Software Initiative of Japan
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
 * Reference:
 *
 * [1] FIPS PUB 202: SHA-3 Standard:
 *                   Permutation-Based Hash and Extendable-Output Functions,
 *                   August 2015.
 */

#define INDEX_MAX(cap) (200 - (cap >> 3))

#define SHAKE256_CAPACITY 512
#define SHAKE256_INDEX_MAX INDEX_MAX (SHAKE256_CAPACITY)

#define SHAKE128_CAPACITY 256
#define SHAKE128_INDEX_MAX INDEX_MAX (SHAKE128_CAPACITY)

#define SHA3_512_CAPACITY 1024
#define SHA3_512_INDEX_MAX INDEX_MAX (SHA3_512_CAPACITY)

/*
 * SHAKE is defined appending 11 at the end to RawSHAKE,
 * RawSHAKE is defined adding 11 at the end to KECCAK,
 * and KECCACK uses pad10*1 at the end.
 * This means adding 111110*1 at the end.
 */
#define SHAKE_SUFFIX 0x1F
#define SHA3_SUFFIX  0x06

/*
 * b=1600
 * nr = 24 iterations
 * l = 6
 *
 * state: 25x64-bit  ==  5 x      5 x  64
 *                       row   column  bit
 */

#include <stdint.h>
#include <string.h>
#include <stdarg.h>
#include "keccak.h"

/* Round constants in iota step.  */
static const uint64_t rc[24] = {
  UINT64_C (0x0000000000000001), UINT64_C (0x0000000000008082),
  UINT64_C (0x800000000000808a), UINT64_C (0x8000000080008000),
  UINT64_C (0x000000000000808b), UINT64_C (0x0000000080000001),
  UINT64_C (0x8000000080008081), UINT64_C (0x8000000000008009),
  UINT64_C (0x000000000000008a), UINT64_C (0x0000000000000088),
  UINT64_C (0x0000000080008009), UINT64_C (0x000000008000000a),
  UINT64_C (0x000000008000808b), UINT64_C (0x800000000000008b),
  UINT64_C (0x8000000000008089), UINT64_C (0x8000000000008003),
  UINT64_C (0x8000000000008002), UINT64_C (0x8000000000000080),
  UINT64_C (0x000000000000800a), UINT64_C (0x800000008000000a),
  UINT64_C (0x8000000080008081), UINT64_C (0x8000000000008080),
  UINT64_C (0x0000000080000001), UINT64_C (0x8000000080008008),
};

static const uint8_t rho[25-1] = {
      1, 62, 28, 27,
 36, 44,  6, 55, 20,
  3, 10, 43, 25, 39,
 41, 45, 15, 21,  8,
 18,  2, 61, 56, 14
};

static const uint8_t pi[24] = {
  10,  7, 11, 17, 18, 3,  5, 16,  8, 21, 24, 4,
  15, 23, 19, 13, 12, 2, 20, 14, 22,  9,  6, 1,
};

static uint64_t
rotl64 (uint64_t x, uint64_t y)
{
  return (x << y) | (x >> (64U - y));
}

static void
absorb (uint64_t *dst, uint8_t index, uint8_t v)
{
  dst[index >> 3] ^= ((uint64_t)v) << ((index & 7) << 3);
}

static uint8_t
squeeze (const uint64_t *src, uint8_t index)
{
  return src[index >> 3] >> ((index & 7) << 3);
}

/* The permutation function.  */
static void
keccak_f1600 (uint64_t s[25])
{
  uint64_t lane[5];
  int i, j, round;

  for (round = 0; round < 24; round++)
    {
      uint64_t t;

      /* STEP: theta */
      for (i = 0; i < 5; i++)
	lane[i] = s[i] ^ s[i + 5] ^ s[i + 10] ^ s[i + 15] ^ s[i + 20];

      for (i = 0; i < 5; i++)
	{
	  t = lane[(i + 4) % 5] ^ rotl64 (lane[(i + 1) % 5], 1);
	  for (j = 0; j < 25; j += 5)
	    s[j + i] ^= t;
	}

      /* STEP: rho */
      for (i = 1; i < 25; i++)
	s[i] = rotl64(s[i], rho[i-1]);

      /* STEP: pi */
      t = s[1];
      for (i = 0; i < 25-1; i++)
	{
	  uint64_t tmp;

	  j = pi[i];
	  tmp = s[j];
	  s[j] = t;
	  t = tmp;
	}

      /* STEP: chi */
      for (i = 0; i < 25; i += 5)
	{
	  for (j = 0; j < 5; j++)
	    lane[j] = s[i + j];
	  for (j = 0; j < 5; j++)
	    s[i + j] ^= (~lane[(j + 1) % 5]) & lane[(j + 2) % 5];
	}

      /* STEP: iota */
      s[0] ^= rc[round];
    }
}

static void
keccak_update (struct keccak_context *keccak,
               const unsigned char *src, unsigned int size)
{
  if (size == 0)
    return;

  while (1)
    {
      absorb (keccak->state, keccak->index, *src++);
      if (++keccak->index == keccak->index_max)
	{
	  keccak_f1600 (keccak->state);
	  keccak->index = 0;
	}
      if (--size == 0)
	break;
    }
}

static void
keccak_finish (struct keccak_context *keccak,
               unsigned char *dst, unsigned int size, uint8_t suffix)
{
  if (size == 0)
    return;

  absorb (keccak->state, keccak->index, suffix);
  absorb (keccak->state, keccak->index_max - 1, 0x80);
  keccak_f1600 (keccak->state);
  keccak->index = 0;

  while (1)
    {
      *dst++ = squeeze (keccak->state, keccak->index);
      if (--size == 0)
	break;
      if (++keccak->index == keccak->index_max)
	{
	  keccak_f1600 (keccak->state);
	  keccak->index = 0;
	}
    }
}

void
shake128_start (struct keccak_context *shake)
{
  memset (shake, 0, sizeof (keccak_context));
  shake->index_max = SHAKE128_INDEX_MAX;
}

void
shake256_start (struct keccak_context *shake)
{
  memset (shake, 0, sizeof (keccak_context));
  shake->index_max = SHAKE256_INDEX_MAX;
}

void
shake128_update (struct keccak_context *shake,
                 const unsigned char *src, unsigned int size)
{
  keccak_update (shake, src, size);
}

void
shake256_update (struct keccak_context *shake,
                 const unsigned char *src, unsigned int size)
{
  keccak_update (shake, src, size);
}

void
shake128_finish (struct keccak_context *shake,
                 unsigned char *dst, unsigned int size)
{
  keccak_finish (shake, dst, size, SHAKE_SUFFIX);
}

void
shake256_finish (struct keccak_context *shake,
                 unsigned char *dst, unsigned int size)
{
  keccak_finish (shake, dst, size, SHAKE_SUFFIX);
}

void
shake256v (uint8_t *out, size_t outlen, ...)
{
  struct keccak_context ctx;
  va_list ap;
  void *p;
  size_t len;

  shake256_start (&ctx);

  va_start (ap, outlen);
  while (1)
    {
      p = va_arg (ap, void *);
      len = va_arg (ap, size_t);
      if (!p)
        break;

      shake256_update (&ctx, p, len);
    }
  va_end (ap);

  shake256_finish (&ctx, out, outlen);
}

void
sha3_512 (uint8_t h[64], const uint8_t *in, size_t inlen)

{
  struct keccak_context ctx;

  memset (&ctx, 0, sizeof (keccak_context));
  ctx.index_max = SHA3_512_INDEX_MAX;

  keccak_update (&ctx, in, inlen);

  keccak_finish (&ctx, h, 64, SHA3_SUFFIX);
}
