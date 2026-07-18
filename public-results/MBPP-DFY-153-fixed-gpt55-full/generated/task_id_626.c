#include <limits.h>

/*@
  requires radius > 0;
  requires radius <= 46340;
  assigns \nothing;
  ensures \result == radius * radius;
*/
int AreaOfLargestTriangleInSemicircle(int radius) {
    int area = radius * radius;
    return area;
}