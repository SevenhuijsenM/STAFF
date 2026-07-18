#include <stdbool.h>

/*@
  requires length >= 0;
  requires length == 0 || \valid_read(a + (0 .. length - 1));
  assigns \nothing;
  ensures \result ==> \forall integer i, j;
            0 <= i && i < length && 0 <= j && j < length ==> a[i] == a[j];
  ensures !\result ==> \exists integer i, j;
            0 <= i && i < length && 0 <= j && j < length && a[i] != a[j];
*/
bool HasOnlyOneDistinctElement(const int *a, int length) {
    if (length == 0) {
        return true;
    }

    int firstElement = a[0];
    int i = 1;

    /*@
      loop invariant 1 <= i;
      loop invariant i <= length;
      loop invariant \forall integer k; 0 <= k && k < i ==> a[k] == firstElement;
      loop assigns i;
      loop variant length - i;
    */
    while (i < length) {
        if (a[i] != firstElement) {
            //@ assert a[0] == firstElement;
            //@ assert a[i] != firstElement;
            //@ assert 0 <= 0 && 0 < length;
            //@ assert 0 <= i && i < length;
            return false;
        }
        i++;
    }

    //@ assert i == length;
    //@ assert \forall integer k; 0 <= k && k < length ==> a[k] == firstElement;
    return true;
}