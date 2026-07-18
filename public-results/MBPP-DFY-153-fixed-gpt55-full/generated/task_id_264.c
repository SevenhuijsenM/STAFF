#include <limits.h>

/*@
  requires humanYears >= 0;
  requires humanYears <= INT_MAX / 7;
  assigns \nothing;
  ensures \result == 7 * humanYears;
*/
int DogYears(int humanYears)
{
    int dogYears = 7 * humanYears;
    return dogYears;
}