#include <stdbool.h>

/*@
  assigns \nothing;
  ensures \result <==> n % 2 == 0;
*/
bool IsEven(int n)
{
    bool result = (n % 2 == 0);
    return result;
}