#include <limits.h>

/*@
  requires 0 <= n;
  requires n < INT_MAX;
  requires 0 <= capacity;
  requires capacity >= n / 3 + 1;
  requires \valid(lucid + (0 .. capacity - 1));

  assigns lucid[0 .. capacity - 1];

  ensures 0 <= \result;
  ensures \result <= capacity;
  ensures \result == n / 3 + 1;
  ensures \forall integer i; 0 <= i && i < \result ==> lucid[i] % 3 == 0;
  ensures \forall integer i; 0 <= i && i < \result ==> lucid[i] <= n;
  ensures \forall integer i, j; 0 <= i && i < j && j < \result ==> lucid[i] < lucid[j];
*/
int LucidNumbers(int n, int *lucid, int capacity)
{
    int len = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n + 1;
      loop invariant 0 <= len;
      loop invariant len <= capacity;
      loop invariant len == (i + 2) / 3;
      loop invariant \forall integer k; 0 <= k && k < len ==> lucid[k] == 3 * k;
      loop invariant \forall integer k; 0 <= k && k < len ==> lucid[k] % 3 == 0;
      loop invariant \forall integer k; 0 <= k && k < len ==> lucid[k] <= i - 1;
      loop invariant \forall integer k, l; 0 <= k && k < l && l < len ==> lucid[k] < lucid[l];
      loop assigns i, len, lucid[0 .. capacity - 1];
      loop variant n - i + 1;
    */
    while (i <= n) {
        if (i % 3 == 0) {
            lucid[len] = i;
            len = len + 1;
        }
        i = i + 1;
    }

    return len;
}