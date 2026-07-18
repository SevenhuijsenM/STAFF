#include <stdbool.h>

/*@
  requires 1 <= month && month <= 12;
  assigns \nothing;
  ensures (\result != 0) <==> (month == 4 || month == 6 || month == 9 || month == 11);
*/
bool IsMonthWith30Days(int month)
{
    bool result = (month == 4 || month == 6 || month == 9 || month == 11);
    return result;
}