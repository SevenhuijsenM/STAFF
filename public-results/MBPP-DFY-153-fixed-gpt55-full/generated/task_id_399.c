#include <stdint.h>
#include <stddef.h>

/*@
  requires a_len == b_len;
  requires a_len == 0 || \valid_read(a + (0 .. (integer)a_len - 1));
  requires a_len == 0 || \valid_read(b + (0 .. (integer)b_len - 1));
  requires a_len == 0 || \valid(result + (0 .. (integer)a_len - 1));
  requires a_len == 0 || \separated(result + (0 .. (integer)a_len - 1), a + (0 .. (integer)a_len - 1));
  requires a_len == 0 || \separated(result + (0 .. (integer)a_len - 1), b + (0 .. (integer)b_len - 1));
  assigns result[0 .. (integer)a_len - 1];
  ensures \result == a_len;
  ensures \forall integer i; 0 <= i && i < (integer)\result ==> result[i] == (a[i] ^ b[i]);
*/
size_t BitwiseXOR(const uint32_t *a, size_t a_len,
                  const uint32_t *b, size_t b_len,
                  uint32_t *result)
{
    size_t i = 0;

    /*@
      loop invariant 0 <= (integer)i && (integer)i <= (integer)a_len;
      loop invariant \forall integer k; 0 <= k && k < (integer)i ==> result[k] == (a[k] ^ b[k]);
      loop assigns i, result[0 .. (integer)a_len - 1];
      loop variant (integer)a_len - (integer)i;
    */
    while (i < a_len) {
        result[i] = a[i] ^ b[i];
        i = i + 1;
    }

    return a_len;
}