#include <stddef.h>

/*@
  predicate IsOddPred(integer n) =
    \exists integer q; n == 2 * q + 1;
*/

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsOddPred(n);
*/
int IsOdd(int n)
{
    if (n % 2 == 0) {
        return 0;
    } else {
        return 1;
    }
}

/*@
  requires length >= 0;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==>
          (\forall integer i;
             0 <= i && i < length ==> (IsOddPred(i) ==> IsOddPred(a[i])));
*/
int IsOddAtIndexOdd(const int *a, int length)
{
    int result = 1;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= length;
      loop invariant result == 0 || result == 1;
      loop invariant (result != 0) <==>
        (\forall integer k;
           0 <= k && k < i ==> (IsOddPred(k) ==> IsOddPred(a[k])));
      loop assigns i, result;
      loop variant length - i;
    */
    while (i < length) {
        if (IsOdd(i) != 0 && IsOdd(a[i]) == 0) {
            result = 0;
        }
        i++;
    }

    return result;
}