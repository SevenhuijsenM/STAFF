#include <stdbool.h>

/*@
  assigns \nothing;
  ensures (\result != 0) <==> (((n % 2 + 2) % 2) == 1);
*/
bool IsOdd(int n)
{
    bool result = (((n % 2 + 2) % 2) == 1);
    return result;
}