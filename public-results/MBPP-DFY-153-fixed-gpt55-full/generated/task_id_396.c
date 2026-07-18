#include <stdbool.h>
#include <stddef.h>

/*@
  requires len > 0;
  requires \valid_read(s + (0 .. len - 1));
  assigns \nothing;
  ensures (\result != 0) <==> (s[0] == s[len - 1]);
*/
bool StartAndEndWithSameChar(const char *s, size_t len)
{
    return s[0] == s[len - 1];
}