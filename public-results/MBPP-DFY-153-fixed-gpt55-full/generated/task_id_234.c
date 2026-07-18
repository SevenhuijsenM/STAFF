#include <limits.h>

/*@
  requires size > 0;
  requires size * size * size <= INT_MAX;
  assigns \nothing;
  ensures \result == size * size * size;
*/
int CubeVolume(int size) {
    int volume = size * size * size;
    return volume;
}