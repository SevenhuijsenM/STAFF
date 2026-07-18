#include <limits.h>

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  requires n == 0 || \valid_read(b + (0 .. n - 1));
  requires n == 0 || \valid(result + (0 .. n - 1));
  requires n == 0 || \separated(result + (0 .. n - 1), a + (0 .. n - 1));
  requires n == 0 || \separated(result + (0 .. n - 1), b + (0 .. n - 1));
  requires \forall integer i; 0 <= i && i < n ==> (integer)a[i] * (integer)b[i] <= INT_MAX;
  requires \forall integer i; 0 <= i && i < n ==> (integer)a[i] * (integer)b[i] >= INT_MIN;
  assigns result[0 .. n - 1];
  ensures \forall integer i; 0 <= i && i < n ==> result[i] == \old(a[i]) * \old(b[i]);
*/
void MultiplyElements(const int *a, const int *b, int *result, int n)
{
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> result[k] == a[k] * b[k];
      loop assigns i, result[0 .. n - 1];
      loop variant n - i;
    */
    while (i < n) {
        result[i] = a[i] * b[i];
        i = i + 1;
    }
}