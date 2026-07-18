#include <stdbool.h>

/*@
  requires length >= 0;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  assigns \nothing;
  ensures \result ==> (\forall integer i; 0 <= i && i < length ==> n > a[i]);
  ensures !\result ==> (\exists integer i; 0 <= i && i < length && n <= a[i]);
*/
bool IsGreater(int n, const int *a, int length) {
    bool result = true;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= length;
      loop invariant result ==> (\forall integer k; 0 <= k && k < i ==> n > a[k]);
      loop invariant !result ==> (\exists integer k; 0 <= k && k < i && n <= a[k]);
      loop assigns i, result;
      loop variant length - i;
    */
    while (i < length) {
        if (n <= a[i]) {
            //@ assert 0 <= i && i < length;
            //@ assert n <= a[i];
            result = false;
            break;
        }
        //@ assert n > a[i];
        i = i + 1;
    }

    return result;
}