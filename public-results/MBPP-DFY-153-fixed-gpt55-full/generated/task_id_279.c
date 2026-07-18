#include <limits.h>

/*@
  requires n >= 0;
  requires n <= 23170;
  assigns \nothing;
  ensures \result == 4 * n * n - 3 * n;
*/
int NthDecagonalNumber(int n)
{
    int decagonal = 4 * n * n - 3 * n;
    return decagonal;
}