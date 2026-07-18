#include <limits.h>

/*@
  predicate dafny_quotient_result(integer a, integer b, integer q) =
    b != 0 &&
    0 <= a - q * b &&
    ((b > 0 && a - q * b < b) || (b < 0 && a - q * b < -b));
*/

/*@
  requires b != 0;
  requires !(a == INT_MIN && b == -1);
  assigns \nothing;
  ensures dafny_quotient_result(a, b, \result);
*/
int Quotient(int a, int b)
{
    int q = a / b;
    int r = a % b;

    if (r < 0) {
        if (b > 0) {
            q = q - 1;
        } else {
            q = q + 1;
        }
    }

    return q;
}