#include <limits.h>

/*@
  requires 0 <= a_len;
  requires a_len % 2 == 0;
  requires a_len == 0 || \valid_read(a + (0 .. a_len - 1));
  requires a_len == 0 || \valid(result + (0 .. a_len / 2 - 1));
  requires a_len == 0 || \separated(a + (0 .. a_len - 1), result + (0 .. a_len / 2 - 1));
  requires \forall integer k;
            0 <= k && k < a_len / 2 ==>
              INT_MIN <= a[2 * k] + a[2 * k + 1] &&
              a[2 * k] + a[2 * k + 1] <= INT_MAX;
  assigns result[0 .. a_len / 2 - 1];
  ensures \forall integer i;
            0 <= i && i < a_len / 2 ==>
              result[i] == a[2 * i] + a[2 * i + 1];
*/
void PairwiseAddition(const int *a, int a_len, int *result)
{
  int i = 0;

  /*@
    loop invariant 0 <= i && i <= a_len / 2;
    loop invariant \forall integer k;
              0 <= k && k < i ==>
                result[k] == a[2 * k] + a[2 * k + 1];
    loop assigns i, result[0 .. a_len / 2 - 1];
    loop variant a_len / 2 - i;
  */
  while (i < a_len / 2) {
    result[i] = a[2 * i] + a[2 * i + 1];
    i = i + 1;
  }
}