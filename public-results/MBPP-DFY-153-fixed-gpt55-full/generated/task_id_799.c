#include <stdint.h>

/*@
  requires 0 <= d;
  requires d < 32;
  assigns \nothing;
  ensures d == 0 ==> \result == n;
  ensures 0 < d ==> \result == (uint32_t)((n << d) | (n >> (32 - d)));
*/
uint32_t RotateLeftBits(uint32_t n, int d) {
    uint32_t result;

    if (d == 0) {
        result = n;
    } else {
        result = (uint32_t)((n << d) | (n >> (32 - d)));
    }

    return result;
}