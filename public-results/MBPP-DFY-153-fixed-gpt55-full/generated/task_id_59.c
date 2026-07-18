#include <limits.h>

/*@
  requires n >= 0;
  requires 3 * n <= INT_MAX;
  requires n * (3 * n - 2) <= INT_MAX;
  assigns \nothing;
  ensures \result == n * (3 * n - 2);
*/
int NthOctagonalNumber(int n)
{
    int octagonalNumber = n * (3 * n - 2);
    return octagonalNumber;
}