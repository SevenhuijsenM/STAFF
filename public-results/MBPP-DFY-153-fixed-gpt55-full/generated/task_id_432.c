#include <limits.h>

/*@
  requires a > 0;
  requires b > 0;
  requires a <= INT_MAX - b;
  assigns \nothing;
  ensures \result == (a + b) / 2;
*/
int MedianLength(int a, int b)
{
    int median = (a + b) / 2;
    return median;
}