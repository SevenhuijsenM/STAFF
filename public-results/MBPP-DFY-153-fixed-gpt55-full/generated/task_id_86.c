#include <limits.h>

/*@
  requires n >= 0;
  requires 3 * n * (n - 1) + 1 <= LLONG_MAX;
  assigns \nothing;
  ensures \result == 3 * n * (n - 1) + 1;
  ensures \result >= 0;
*/
long long CenteredHexagonalNumber(long long n)
{
    long long result = 3 * n * (n - 1) + 1;
    return result;
}