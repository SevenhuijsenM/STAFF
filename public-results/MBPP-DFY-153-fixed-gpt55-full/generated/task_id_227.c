/*@
  assigns \nothing;
  ensures \result <= a && \result <= b && \result <= c;
  ensures \result == a || \result == b || \result == c;
*/
int MinOfThree(int a, int b, int c) {
    int min;

    if (a <= b && a <= c) {
        min = a;
    } else if (b <= a && b <= c) {
        min = b;
    } else {
        min = c;
    }

    return min;
}