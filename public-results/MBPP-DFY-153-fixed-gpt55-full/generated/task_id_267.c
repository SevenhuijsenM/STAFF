#include <limits.h>

/*@
  requires 0 <= n;
  requires n <= 1172;
  assigns \nothing;
  ensures \result == (n * (2 * n - 1) * (2 * n + 1)) / 3;
*/
int SumOfSquaresOfFirstNOddNumbers(int n)
{
    long long sum = 0;
    long long i = 1;
    int k = 0;

    /*@
      loop invariant 0 <= n;
      loop invariant n <= 1172;
      loop invariant 0 <= k && k <= n;
      loop invariant sum == (k * (2 * k - 1) * (2 * k + 1)) / 3;
      loop invariant i == 2 * k + 1;
      loop invariant 0 <= sum && sum <= INT_MAX;
      loop invariant 1 <= i && i <= 2345;
      loop assigns k, sum, i;
      loop variant n - k;
    */
    while (k < n) {
        sum = sum + i * i;
        i = i + 2;
        k = k + 1;
    }

    //@ assert 0 <= sum;
    //@ assert sum <= INT_MAX;
    return (int)sum;
}