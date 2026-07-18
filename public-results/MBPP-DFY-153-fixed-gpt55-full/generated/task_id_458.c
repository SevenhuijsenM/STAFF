#include <limits.h>

/*@
  requires length > 0;
  requires width > 0;
  requires length <= INT_MAX / width;
  assigns \nothing;
  ensures \result == length * width;
*/
int RectangleArea(int length, int width) {
    int area = length * width;
    return area;
}