#include <limits.h>

/*@
  requires n > 1;
  requires \valid_read(a + (0 .. n - 1));
  requires \forall integer i, j;
            0 <= i && i < n && 0 <= j && j < n ==>
            ((integer)a[i]) - ((integer)a[j]) <= INT_MAX;
  assigns \nothing;
  ensures \forall integer i, j;
            0 <= i && i < n && 0 <= j && j < n ==>
            ((integer)a[i]) - ((integer)a[j]) <= \result;
*/
int MaxDifference(const int *a, int n)
{
    int minVal = a[0];
    int maxVal = a[0];
    int i;

    /*@
      loop invariant 1 <= i && i <= n;
      loop invariant minVal <= maxVal;
      loop invariant \forall integer k;
                        0 <= k && k < i ==> minVal <= a[k];
      loop invariant \forall integer k;
                        0 <= k && k < i ==> a[k] <= maxVal;
      loop invariant \exists integer k;
                        0 <= k && k < i && minVal == a[k];
      loop invariant \exists integer k;
                        0 <= k && k < i && maxVal == a[k];
      loop invariant 0 <= ((integer)maxVal) - ((integer)minVal);
      loop invariant ((integer)maxVal) - ((integer)minVal) <= INT_MAX;
      loop assigns i, minVal, maxVal;
      loop variant n - i;
    */
    for (i = 1; i < n; i++) {
        if (a[i] < minVal) {
            minVal = a[i];
        } else if (a[i] > maxVal) {
            maxVal = a[i];
        }
    }

    return maxVal - minVal;
}