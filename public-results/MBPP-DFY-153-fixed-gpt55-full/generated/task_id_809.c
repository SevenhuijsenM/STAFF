#include <stdbool.h>

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  requires n == 0 || \valid_read(b + (0 .. n - 1));
  assigns \nothing;
  ensures (\result != 0) <==> (\forall integer i; 0 <= i && i < n ==> a[i] > b[i]);
  ensures (\result == 0) <==> (\exists integer i; 0 <= i && i < n && a[i] <= b[i]);
*/
bool IsSmaller(const int *a, const int *b, int n)
{
    bool result = true;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant (result != 0) <==> (\forall integer k; 0 <= k && k < i ==> a[k] > b[k]);
      loop invariant (result == 0) <==> (\exists integer k; 0 <= k && k < i && a[k] <= b[k]);
      loop assigns i, result;
      loop variant n - i;
    */
    while (i < n && result) {
        if (a[i] <= b[i]) {
            result = false;
        }
        i++;
    }

    return result;
}