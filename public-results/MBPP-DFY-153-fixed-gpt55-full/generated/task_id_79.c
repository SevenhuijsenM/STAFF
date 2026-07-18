#include <stdbool.h>
#include <stddef.h>

/*@
  requires len == 0 || \valid_read(s + (0 .. len - 1));
  assigns \nothing;
  ensures (\result == 1) <==> (len % 2 == 1);
  ensures (\result == 0) <==> (len % 2 == 0);
*/
bool IsLengthOdd(const char *s, size_t len)
{
    (void)s;
    bool result = (len % 2u) == 1u;
    return result;
}