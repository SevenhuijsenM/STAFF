#include <stdbool.h>

/*@
  assigns \nothing;
  ensures (\result == 1) <==> ((a < 0 && b > 0) || (a > 0 && b < 0));
*/
bool HasOppositeSign(int a, int b) {
  bool result = (a < 0 && b > 0) || (a > 0 && b < 0);
  return result;
}