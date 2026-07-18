#include <limits.h>

/*@
  requires INT_MIN <= a * b && a * b <= INT_MAX;
  assigns \nothing;
  ensures \result == a * b;
*/
int Multiply(int a, int b) {
  int result = a * b;
  return result;
}