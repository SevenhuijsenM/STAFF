#include <stdbool.h>

/*@
  lemma divisor_bounded_by_half:
    \forall integer n, k;
      2 <= n && 2 <= k && k < n && n % k == 0 ==> k <= n / 2;
*/

/*@
  requires n >= 2;
  assigns \nothing;
  ensures (\result != 0) <==> (\exists integer k; 2 <= k && k < n && n % k == 0);
*/
bool IsNonPrime(int n)
{
    bool result = false;
    int i = 2;

    /*@
      loop invariant 2 <= i;
      loop invariant i <= n / 2 + 1;
      loop invariant (result != 0) <==> (\exists integer k; 2 <= k && k < i && n % k == 0);
      loop assigns i, result;
      loop variant n / 2 - i + 1;
    */
    while (i <= n / 2) {
        if (n % i == 0) {
            result = true;
            break;
        }
        i = i + 1;
    }

    return result;
}