#include <stdbool.h>

/*@
  requires n >= 0;
  assigns \nothing;
  ensures \result != 0 ==> (\exists integer i; 0 <= i && i <= n && i * i == n);
  ensures \result == 0 ==> (\forall integer a; 0 < a * a && a * a < n ==> a * a != n);
*/
bool IsPerfectSquare(int n)
{
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> k * k < n;
      loop assigns i;
      loop variant n - i;
    */
    while ((long long)i * (long long)i < (long long)n) {
        i = i + 1;
    }

    return ((long long)i * (long long)i == (long long)n);
}