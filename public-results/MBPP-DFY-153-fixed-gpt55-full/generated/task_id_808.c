#include <stdbool.h>

/*@
  requires 0 <= n;
  requires n == 0 || \valid_read(s + (0 .. n-1));
  assigns \nothing;
  ensures (\result != 0) <==> (\exists integer j; 0 <= j && j < n && s[j] == k);
*/
bool ContainsK(const int *s, int n, int k)
{
    bool result = false;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant (result != 0) <==> (\exists integer j; 0 <= j && j < i && s[j] == k);
      loop assigns i, result;
      loop variant n - i;
    */
    while (i < n && !result) {
        if (s[i] == k) {
            result = true;
        }
        i++;
    }

    return result;
}