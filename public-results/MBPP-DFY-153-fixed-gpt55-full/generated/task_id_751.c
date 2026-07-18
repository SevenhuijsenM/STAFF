#include <stdbool.h>

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n-1));
  assigns \nothing;
  ensures \result == true ==>
            \forall integer i;
              0 <= i && i < n / 2 ==>
                a[i] <= a[2 * i + 1] &&
                (2 * i + 2 == n || a[i] <= a[2 * i + 2]);
  ensures \result == false ==>
            \exists integer i;
              0 <= i && i < n / 2 &&
                (a[i] > a[2 * i + 1] ||
                 (2 * i + 2 != n && a[i] > a[2 * i + 2]));
*/
bool IsMinHeap(const int *a, int n)
{
  bool result = true;
  int i = 0;

  /*@
    loop invariant 0 <= i && i <= n / 2;
    loop invariant result == true ==>
              \forall integer k;
                0 <= k && k < i ==>
                  a[k] <= a[2 * k + 1] &&
                  (2 * k + 2 == n || a[k] <= a[2 * k + 2]);
    loop invariant result == false ==>
              \exists integer k;
                0 <= k && k < n / 2 &&
                  (a[k] > a[2 * k + 1] ||
                   (2 * k + 2 != n && a[k] > a[2 * k + 2]));
    loop assigns i, result;
    loop variant n / 2 - i;
  */
  while (i < n / 2 && result) {
    if (a[i] > a[2 * i + 1] ||
        (2 * i + 2 != n && a[i] > a[2 * i + 2])) {
      result = false;
    }
    i++;
  }

  return result;
}