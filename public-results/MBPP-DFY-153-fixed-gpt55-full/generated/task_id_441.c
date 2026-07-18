#include <limits.h>

/*@
  requires size > 0;
  requires 6 * size * size <= INT_MAX;
  assigns \nothing;
  ensures \result == 6 * size * size;
*/
int CubeSurfaceArea(int size)
{
    int area = 6 * size * size;
    return area;
}