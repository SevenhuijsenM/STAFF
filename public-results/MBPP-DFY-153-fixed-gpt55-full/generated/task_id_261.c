#include <limits.h>

/*@
  predicate DafnyDivision(integer x, integer y, integer q) =
    y != 0 &&
    (\exists integer r;
       0 <= r &&
       r < (y < 0 ? -y : y) &&
       x == y * q + r);
*/

/*@
  requires y != 0;
  requires !(x == INT_MIN && y == -1);
  assigns \nothing;
  ensures DafnyDivision(x, y, \result);
*/
static int DafnyDiv(int x, int y)
{
    int q = x / y;
    int r = x % y;

    if (r < 0) {
        if (y > 0) {
            q = q - 1;
            r = r + y;
        } else {
            q = q + 1;
            r = r - y;
        }
    }

    return q;
}

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n-1));
  requires n == 0 || \valid_read(b + (0 .. n-1));
  requires n == 0 || \valid(result + (0 .. n-1));
  requires n > 0 ==> \separated(a + (0 .. n-1), result + (0 .. n-1));
  requires n > 0 ==> \separated(b + (0 .. n-1), result + (0 .. n-1));
  requires \forall integer i; 0 <= i && i < n ==> b[i] != 0;
  requires \forall integer i; 0 <= i && i < n ==> !(a[i] == INT_MIN && b[i] == -1);
  assigns result[0 .. n-1];
  ensures \result == n;
  ensures \forall integer i; 0 <= i && i < \result ==> DafnyDivision(\old(a[i]), \old(b[i]), result[i]);
*/
int ElementWiseDivision(const int *a, const int *b, int n, int *result)
{
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> DafnyDivision(a[k], b[k], result[k]);
      loop assigns i, result[0 .. n-1];
      loop variant n - i;
    */
    while (i < n) {
        result[i] = DafnyDiv(a[i], b[i]);
        i = i + 1;
    }

    return n;
}