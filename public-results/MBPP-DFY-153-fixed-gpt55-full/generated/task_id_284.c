#include <stdbool.h>

/*@
  requires length >= 0;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  assigns \nothing;
  ensures \result != 0 ==> \forall integer i; 0 <= i && i < length ==> a[i] == n;
  ensures \result == 0 ==> \exists integer i; 0 <= i && i < length && a[i] != n;
*/
bool AllElementsEqual(const int *a, int length, int n)
{
    bool result = true;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= length;
      loop invariant result != 0 ==> \forall integer k; 0 <= k && k < i ==> a[k] == n;
      loop invariant result == 0 ==> \exists integer k; 0 <= k && k < i && a[k] != n;
      loop assigns i, result;
      loop variant length - i;
    */
    while (i < length && result) {
        if (a[i] != n) {
            result = false;
        }
        i++;
    }

    return result;
}