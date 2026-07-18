/*@
  assigns \nothing;
  ensures \result == a || \result == b;
  ensures \result >= a && \result >= b;
*/
int Max(int a, int b) {
    int maxValue;
    if (a >= b) {
        maxValue = a;
    } else {
        maxValue = b;
    }
    return maxValue;
}