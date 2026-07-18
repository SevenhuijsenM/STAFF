#include <stdbool.h>

/*@
  lemma large_divisor_mod_nonzero:
    \forall integer m, d;
      2 <= m && m / 2 < d && d < m ==> m % d != 0;
*/

/*@
  requires n >= 2;
  assigns \nothing;
  ensures ((\result == true) <==> (\forall integer k; 2 <= k && k < n ==> n % k != 0));
*/
bool IsPrime(int n)
{
    bool result = true;
    int i = 2;

    /*@
      loop invariant 2 <= i;
      loop invariant i <= n / 2 + 1;
      loop invariant result == true;
      loop invariant ((result == true) <==> (\forall integer k; 2 <= k && k < i ==> n % k != 0));
      loop invariant \forall integer k; n / 2 < k && k < n ==> n % k != 0;
      loop assigns i, result;
      loop variant n / 2 - i + 1;
    */
    while (i <= n / 2) {
        if (n % i == 0) {
            result = false;
            //@ assert 2 <= i;
            //@ assert i <= n / 2;
            //@ assert i < n;
            //@ assert n % i == 0;
            //@ assert !(\forall integer k; 2 <= k && k < n ==> n % k != 0);
            return result;
        }
        i = i + 1;
    }

    //@ assert result == true;
    //@ assert i == n / 2 + 1;
    //@ assert \forall integer k; 2 <= k && k < i ==> n % k != 0;
    //@ assert \forall integer k; n / 2 < k && k < n ==> n % k != 0;
    //@ assert \forall integer k; 2 <= k && k < n ==> n % k != 0;
    return result;
}