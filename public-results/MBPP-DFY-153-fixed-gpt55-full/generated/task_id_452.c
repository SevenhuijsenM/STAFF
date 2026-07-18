/*@
  requires costPrice >= 0;
  requires sellingPrice >= 0;
  assigns \nothing;
  ensures costPrice > sellingPrice ==> \result == costPrice - sellingPrice;
  ensures costPrice <= sellingPrice ==> \result == 0;
*/
int CalculateLoss(int costPrice, int sellingPrice) {
  int loss;

  if (costPrice > sellingPrice) {
    loss = costPrice - sellingPrice;
  } else {
    loss = 0;
  }

  return loss;
}