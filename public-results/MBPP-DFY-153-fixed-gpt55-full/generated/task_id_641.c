#include <limits.h>

/*@
  requires n >= 0;
  requires 7 * (integer)n <= INT_MAX;
  requires INT_MIN <= (integer)n * (7 * (integer)n - 5);
  requires (integer)n * (7 * (integer)n - 5) <= INT_MAX;
  assigns \nothing;
  ensures \result == ((integer)n * (7 * (integer)n - 5)) / 2;
*/
int NthNonagonalNumber(int n) {
  int number = n * (7 * n - 5) / 2;
  return number;
}