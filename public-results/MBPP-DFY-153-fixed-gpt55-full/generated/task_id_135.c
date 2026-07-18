#include <limits.h>

/*@
  requires n >= 0;
  requires 2 * n <= INT_MAX;
  requires n * (2 * n - 1) <= INT_MAX;
  assigns \nothing;
  ensures \result == n * ((2 * n) - 1);
*/
int NthHexagonalNumber(int n)
{
    int hexNum = n * ((2 * n) - 1);
    return hexNum;
}