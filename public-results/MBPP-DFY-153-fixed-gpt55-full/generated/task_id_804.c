#include <stdbool.h>

/*@ predicate IsEven_pred(integer n) = n % 2 == 0; */

/*@
  assigns \nothing;
  ensures (\result != 0) <==> IsEven_pred(n);
*/
bool IsEven(int n)
{
    return (n % 2) == 0;
}

/*@
  requires length >= 0;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  assigns \nothing;
  ensures (\result != 0) <==> (\exists integer i; 0 <= i && i < length && IsEven_pred(a[i]));
*/
bool IsProductEven(const int *a, int length)
{
    bool result = false;
    int i;

    /*@
      loop invariant 0 <= i && i <= length;
      loop invariant (result != 0) <==> (\exists integer k; 0 <= k && k < i && IsEven_pred(a[k]));
      loop assigns i, result;
      loop variant length - i;
    */
    for (i = 0; i < length; i++) {
        if (IsEven(a[i])) {
            //@ assert 0 <= i && i < length;
            //@ assert IsEven_pred(a[i]);
            result = true;
            //@ assert \exists integer k; 0 <= k && k < length && IsEven_pred(a[k]);
            break;
        }
    }

    return result;
}