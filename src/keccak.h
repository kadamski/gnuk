#include <stdint.h>

struct keccak_context {
  uint64_t state[25];
  uint32_t index     : 8;
  uint32_t index_max : 8;
};
typedef struct keccak_context keccak_context;

void shake128_start (struct keccak_context *keccak);
void shake128_update (struct keccak_context *keccak,
		      const unsigned char *src, unsigned int size);
void shake128_finish (struct keccak_context *keccak,
		      unsigned char *dst, unsigned int size);

void shake256_start (struct keccak_context *keccak);
void shake256_update (struct keccak_context *keccak,
		      const unsigned char *src, unsigned int size);
void shake256_finish (struct keccak_context *keccak,
		      unsigned char *dst, unsigned int size);

void shake256v (uint8_t *out, size_t outlen, ...);

void sha3_512 (uint8_t h[64], const uint8_t *in, size_t inlen);
