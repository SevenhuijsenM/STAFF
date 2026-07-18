#include <limits.h>

/*@
  requires side > 0;
  requires side <= INT_MAX / 4;
  assigns \nothing;
  ensures \result == 4 * side;
*/
int SquarePerimeter(int side) {
    int perimeter = 4 * side;
    return perimeter;
}