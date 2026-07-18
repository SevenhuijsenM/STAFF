#include <limits.h>

/*@
  logic integer odd_value(integer k) = 2 * k + 1;

  logic integer fourth_odd(integer k) =
    odd_value(k) * odd_value(k) * odd_value(k) * odd_value(k);

  logic integer fourth_odd_sum(integer k) =
    k * (2 * k + 1) *
    (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15;

  axiomatic SumFourthOddFacts {
    axiom odd_value_step:
      \forall integer k;
        odd_value(k + 1) == odd_value(k) + 2;

    axiom fourth_odd_sum_step:
      \forall integer k;
        0 <= k ==>
          fourth_odd_sum(k + 1) == fourth_odd_sum(k) + fourth_odd(k);

    axiom fourth_odd_sum_bound_58:
      \forall integer k;
        0 <= k && k <= 58 ==>
          0 <= fourth_odd_sum(k) && fourth_odd_sum(k) <= 2147483647;

    axiom small_power_bounds:
      \forall integer x;
        0 <= x && x <= 115 ==>
          0 <= x * x &&
          x * x <= 13225 &&
          0 <= x * x * x &&
          x * x * x <= 1520875 &&
          0 <= x * x * x * x &&
          x * x * x * x <= 174900625;
  }
*/

/*@
  requires n > 0;
  requires n <= 58;
  assigns \nothing;
  ensures 0 <= \result;
  ensures \result == fourth_odd_sum(n);
  ensures \result == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15;
*/
int SumOfFourthPowerOfOddNumbers(int n)
{
    long long sum = 0;
    long long term = 0;
    long long i = 1;
    long long k = 0;

    /*@
      loop invariant n > 0;
      loop invariant n <= 58;
      loop invariant 0 <= k;
      loop invariant k <= n;
      loop invariant i == odd_value(k);
      loop invariant 1 <= i;
      loop invariant i <= 117;
      loop invariant sum == fourth_odd_sum(k);
      loop invariant 0 <= sum;
      loop invariant sum <= 2147483647;
      loop assigns k, i, sum, term;
      loop variant n - k;
    */
    while (k < n) {
        //@ assert 0 <= k;
        //@ assert k < n;
        //@ assert k + 1 <= n;
        //@ assert k + 1 <= 58;
        //@ assert k <= 57;
        //@ assert i == odd_value(k);
        //@ assert 0 <= i;
        //@ assert i <= 115;
        //@ assert 0 <= i * i;
        //@ assert i * i <= 13225;
        //@ assert 0 <= i * i * i;
        //@ assert i * i * i <= 1520875;
        //@ assert 0 <= i * i * i * i;
        //@ assert i * i * i * i <= 174900625;
        //@ assert fourth_odd(k) == i * i * i * i;

        term = i * i * i * i;

        //@ assert term == i * i * i * i;
        //@ assert term == fourth_odd(k);
        //@ assert 0 <= term;
        //@ assert term <= 174900625;
        //@ assert fourth_odd_sum(k + 1) == fourth_odd_sum(k) + fourth_odd(k);
        //@ assert fourth_odd_sum(k + 1) == sum + term;
        //@ assert 0 <= fourth_odd_sum(k + 1);
        //@ assert fourth_odd_sum(k + 1) <= 2147483647;
        //@ assert 0 <= sum + term;
        //@ assert sum + term <= 2147483647;

        sum = sum + term;

        //@ assert sum == fourth_odd_sum(k + 1);
        //@ assert 0 <= sum;
        //@ assert sum <= 2147483647;
        //@ assert i <= 115;
        //@ assert i <= 9223372036854775805LL;
        //@ assert odd_value(k + 1) == odd_value(k) + 2;

        i = i + 2;

        //@ assert i == odd_value(k + 1);
        //@ assert 1 <= i;
        //@ assert i <= 117;
        //@ assert k <= 57;
        //@ assert k <= 9223372036854775806LL;

        k = k + 1;

        //@ assert 0 <= k;
        //@ assert k <= n;
        //@ assert i == odd_value(k);
        //@ assert sum == fourth_odd_sum(k);
    }

    //@ assert k == n;
    //@ assert sum == fourth_odd_sum(n);
    //@ assert 0 <= sum;
    //@ assert sum <= 2147483647;

    return (int)sum;
}