#include <stdbool.h>

/*@
  requires len >= 0;
  requires len == 0 || \valid_read(s + (0 .. len - 1));
  assigns \nothing;
  ensures \result == true ==> (\exists integer i; 0 <= i && i < len && s[i] == '.' && len - i - 1 == 2);
  ensures \result == false ==> !(\exists integer i; 0 <= i && i < len && s[i] == '.' && len - i - 1 == 2);
*/
bool IsDecimalWithTwoPrecision(const char *s, int len)
{
    bool result = false;
    int i;

    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant (result == true) <==> (\exists integer k; 0 <= k && k < i && s[k] == '.' && len - k - 1 == 2);
      loop assigns i, result;
      loop variant len - i;
    */
    for (i = 0; i < len; i++) {
        if (s[i] == '.' && len - i - 1 == 2) {
            result = true;
            //@ assert \exists integer k; 0 <= k && k < len && s[k] == '.' && len - k - 1 == 2;
            break;
        }
    }

    //@ assert result == true ==> (\exists integer k; 0 <= k && k < len && s[k] == '.' && len - k - 1 == 2);
    //@ assert result == false ==> !(\exists integer k; 0 <= k && k < len && s[k] == '.' && len - k - 1 == 2);

    return result;
}