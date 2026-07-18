/*@
  requires n >= 0;
  requires n <= 2343;
  assigns \nothing;
  ensures \result == n * (n + 1) * (n + 2) / 6;
*/
int TetrahedralNumber(int n) {
    long long value = ((long long)n * (n + 1) * (n + 2)) / 6;
    return (int)value;
}