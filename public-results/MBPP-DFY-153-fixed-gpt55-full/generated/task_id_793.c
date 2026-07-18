#include <stddef.h>

/*@
  requires length > 0;
  requires \valid_read(arr + (0 .. length - 1));
  requires \forall integer i, j; 0 <= i && i < j && j < length ==> arr[i] <= arr[j];
  assigns \nothing;
  ensures \result == -1 || (0 <= \result && \result < length && arr[\result] == elem && (\result <= length - 1 || arr[\result + 1] > elem));
  ensures \result == -1 || (0 <= \result && \result < length && arr[\result] == elem && (\result + 1 < length ==> arr[\result + 1] > elem));
  ensures \forall integer k; 0 <= k && k < length ==> arr[k] == \old(arr[k]);
*/
int LastPosition(int *arr, int length, int elem)
{
    int pos = -1;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= length;
      loop invariant pos == -1 || (0 <= pos && pos < i && arr[pos] == elem && (pos + 1 < i ==> arr[pos + 1] > elem));
      loop invariant pos == -1 ==> \forall integer k; 0 <= k && k < i ==> arr[k] != elem;
      loop invariant \forall integer k; 0 <= k && k < i && arr[k] == elem ==> pos != -1 && k <= pos;
      loop invariant \forall integer k; 0 <= k && k < length ==> arr[k] == \at(arr[k], Pre);
      loop assigns i, pos;
      loop variant length - i;
    */
    for (; i < length; i++) {
        if (arr[i] == elem) {
            pos = i;
        }
    }

    return pos;
}