#include <stdbool.h>

/*@
  assigns \nothing;
  ensures (\result != 0) <==> (n % 11 == 0);
*/
bool IsDivisibleBy11(int n)
{
  bool result = (n % 11 == 0);
  return result;
}