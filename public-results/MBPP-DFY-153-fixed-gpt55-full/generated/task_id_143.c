#include <limits.h>

typedef struct {
  int *data;
  int length;
} IntArray;

/*@
  requires arrays_len >= 0;
  requires arrays_len == 0 || \valid_read(arrays + (0 .. arrays_len - 1));
  assigns \nothing;
  ensures \result >= 0;
  ensures \result == arrays_len;
*/
int CountArrays(const IntArray *arrays, int arrays_len) {
  (void)arrays;
  return arrays_len;
}