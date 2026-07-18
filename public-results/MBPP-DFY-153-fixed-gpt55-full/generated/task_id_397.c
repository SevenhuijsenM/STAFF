/*@
  assigns \nothing;
  ensures \result == a || \result == b || \result == c;
  ensures (\result >= a && \result <= b) ||
          (\result >= b && \result <= a) ||
          (\result >= a && \result <= c) ||
          (\result >= c && \result <= a) ||
          (\result >= b && \result <= c) ||
          (\result >= c && \result <= b);
*/
int MedianOfThree(int a, int b, int c)
{
    int median;

    if ((a <= b && b <= c) || (c <= b && b <= a)) {
        median = b;
    } else if ((b <= a && a <= c) || (c <= a && a <= b)) {
        median = a;
    } else {
        median = c;
    }

    return median;
}