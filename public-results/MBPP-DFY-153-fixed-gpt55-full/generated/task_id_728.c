#include <limits.h>

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n-1));
  requires n == 0 || \valid_read(b + (0 .. n-1));
  requires n == 0 || \valid(result + (0 .. n-1));
  requires n == 0 || \separated(result + (0 .. n-1), a + (0 .. n-1));
  requires n == 0 || \separated(result + (0 .. n-1), b + (0 .. n-1));
  requires \forall integer i; 0 <= i && i < n ==> INT_MIN <= a[i] + b[i] && a[i] + b[i] <= INT_MAX;
  assigns result[0 .. n-1];
  ensures \result == n;
  ensures \forall integer i; 0 <= i && i < n ==> result[i] == a[i] + b[i];
*/
int AddLists(const int *a, const int *b, int n, int *result)
{
    int i;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> result[k] == a[k] + b[k];
      loop assigns i, result[0 .. n-1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        result[i] = a[i] + b[i];
    }

    return n;
}