#include <stdbool.h>

/*@
  requires costPrice >= 0;
  requires sellingPrice >= 0;
  assigns \nothing;
  ensures ((\result != 0) <==> (costPrice == sellingPrice));
*/
bool IsBreakEven(int costPrice, int sellingPrice)
{
    return costPrice == sellingPrice;
}