#include <stdbool.h>

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(s + (0 .. n-1));
  assigns \nothing;
  ensures \result ==> (\forall integer i; \forall integer j;
            0 <= i && i < n && 0 <= j && j < n ==> s[i] == s[j]);
  ensures !\result ==> (n > 1 &&
            (\exists integer i; \exists integer j;
              0 <= i && i < n &&
              0 <= j && j < n &&
              i != j &&
              s[i] != s[j]));
*/
bool AllCharactersSame(const char *s, int n)
{
    if (n <= 1) {
        return true;
    }

    char firstChar = s[0];
    bool result = true;
    int i = 1;

    /*@
      loop invariant n > 1;
      loop invariant 1 <= i && i <= n;
      loop invariant firstChar == s[0];
      loop invariant result ==> (\forall integer k;
                0 <= k && k < i ==> s[k] == firstChar);
      loop invariant !result ==> (\exists integer k;
                1 <= k && k < i && s[k] != firstChar);
      loop assigns i, result;
      loop variant n - i;
    */
    while (i < n && result) {
        if (s[i] != firstChar) {
            result = false;
        }
        i++;
    }

    return result;
}