#include <stdbool.h>

/*@
  requires 1 <= month && month <= 12;
  assigns \nothing;
  ensures \result == ((month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12) ? true : false);
*/
bool MonthHas31Days(int month)
{
    bool result = (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12);
    return result;
}