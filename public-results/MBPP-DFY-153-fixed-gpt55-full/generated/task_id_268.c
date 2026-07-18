#include <limits.h>

/*@
  requires n >= 0;
  requires 6 * n * (n - 1) + 1 <= INT_MAX;
  assigns \nothing;
  ensures \result == 6 * n * (n - 1) + 1;
*/
int StarNumber(int n) {
  int star = 6 * n * (n - 1) + 1;
  return star;
}