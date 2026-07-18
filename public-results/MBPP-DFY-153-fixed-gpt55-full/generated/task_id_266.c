#include <limits.h>

/*@
  requires size > 0;
  requires 4 * (integer)size * (integer)size <= INT_MAX;
  assigns \nothing;
  ensures \result == 4 * (integer)size * (integer)size;
*/
int LateralSurfaceArea(int size)
{
    int area = 4 * size * size;
    return area;
}