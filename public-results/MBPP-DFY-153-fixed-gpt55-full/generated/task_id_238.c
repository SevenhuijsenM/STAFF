#include <limits.h>

/*@
  requires len >= 0;
  requires len == 0 || \valid_read(s + (0 .. len - 1));
  requires (len * (len + 1)) / 2 <= INT_MAX;
  assigns \nothing;
  ensures \result >= 0;
  ensures \result == (len * (len + 1)) / 2;
*/
int CountNonEmptySubstrings(const char *s, int len)
{
    (void)s;
    long long n = (long long)len;
    long long count = (n * (n + 1LL)) / 2LL;
    return (int)count;
}