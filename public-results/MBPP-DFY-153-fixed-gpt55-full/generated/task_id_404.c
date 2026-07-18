/*@
  assigns \nothing;
  ensures \result == a || \result == b;
  ensures \result <= a && \result <= b;
*/
int Min(int a, int b) {
    int minValue;

    if (a <= b) {
        minValue = a;
    } else {
        minValue = b;
    }

    return minValue;
}