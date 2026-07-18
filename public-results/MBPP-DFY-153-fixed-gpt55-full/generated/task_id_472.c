#include <stdbool.h>

/*@
  requires n > 0;
  requires \valid_read(a + (0 .. n - 1));
  assigns \nothing;
  ensures (\result != 0) <==> (\exists integer i; 0 <= i && i < n - 1 && (integer)a[i] + 1 == (integer)a[i + 1]);
*/
bool ContainsConsecutiveNumbers(const int *a, int n)
{
    bool result = false;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= n - 1;
      loop invariant (result != 0) <==> (\exists integer k; 0 <= k && k < i && (integer)a[k] + 1 == (integer)a[k + 1]);
      loop assigns i, result;
      loop variant (n - 1) - i;
    */
    for (i = 0; i < n - 1; i++) {
        if ((long long)a[i] + 1LL == (long long)a[i + 1]) {
            result = true;
            //@ assert 0 <= i && i < n - 1;
            //@ assert (integer)a[i] + 1 == (integer)a[i + 1];
            break;
        }
    }

    return result;
}