#include <limits.h>

/*@
  requires baseEdge > 0;
  requires height > 0;
  requires baseEdge * baseEdge <= INT_MAX;
  requires 2 * baseEdge <= INT_MAX;
  requires 2 * baseEdge * height <= INT_MAX;
  requires baseEdge * baseEdge + 2 * baseEdge * height <= INT_MAX;
  assigns \nothing;
  ensures \result == baseEdge * baseEdge + 2 * baseEdge * height;
*/
int SquarePyramidSurfaceArea(int baseEdge, int height)
{
    int area = baseEdge * baseEdge + 2 * baseEdge * height;
    return area;
}