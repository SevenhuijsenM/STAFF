/*@
  requires n >= 0;
  assigns \nothing;
  ensures 0 <= \result && \result < 10;
  ensures n % 10 == \result;
*/
int LastDigit(int n)
{
  int d = n % 10;
  return d;
}