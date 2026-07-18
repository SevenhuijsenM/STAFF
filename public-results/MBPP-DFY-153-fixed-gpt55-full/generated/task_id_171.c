#include <limits.h>

/*@
  requires side > 0;
  requires side <= INT_MAX / 5;
  assigns \nothing;
  ensures \result == 5 * side;
*/
int PentagonPerimeter(int side) {
    int perimeter = 5 * side;
    return perimeter;
}