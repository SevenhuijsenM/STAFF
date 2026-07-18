#include <limits.h>

/*@
  requires base > 0;
  requires height > 0;
  requires length > 0;
  requires base <= INT_MAX / height;
  requires base * height <= INT_MAX / length;
  assigns \nothing;
  ensures \result == (base * height * length) / 2;
*/
int TriangularPrismVolume(int base, int height, int length) {
    int volume = (base * height * length) / 2;
    return volume;
}