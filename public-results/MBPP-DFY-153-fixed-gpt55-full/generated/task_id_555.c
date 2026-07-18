#include <limits.h>

/*@
  axiomatic DifferenceSumFacts {
    axiom sum_cubes_bounds:
      \forall integer k;
        1 <= k && k <= 304 ==>
          0 <= ((k - 1) * (k - 1) * k * k) / 4
          && ((k - 1) * (k - 1) * k * k) / 4 <= 2147483647;

    axiom sum_numbers_bounds:
      \forall integer k;
        1 <= k && k <= 304 ==>
          0 <= ((k - 1) * k) / 2
          && ((k - 1) * k) / 2 <= 2147483647;

    axiom sum_cubes_next_bounds:
      \forall integer k;
        1 <= k && k <= 303 ==>
          0 <= (k * k * (k + 1) * (k + 1)) / 4
          && (k * k * (k + 1) * (k + 1)) / 4 <= 2147483647;

    axiom sum_numbers_next_bounds:
      \forall integer k;
        1 <= k && k <= 303 ==>
          0 <= (k * (k + 1)) / 2
          && (k * (k + 1)) / 2 <= 2147483647;

    axiom diff_bounds:
      \forall integer k;
        0 <= k && k <= 303 ==>
          0 <= (k * k * (k + 1) * (k + 1)) / 4 - (k * (k + 1)) / 2
          && (k * k * (k + 1) * (k + 1)) / 4 - (k * (k + 1)) / 2 <= 2147483647;

    axiom cube_product_long_long_bounds:
      \forall integer k;
        1 <= k && k <= 303 ==>
          0 <= k * k * (k + 1) * (k + 1)
          && k * k * (k + 1) * (k + 1) <= 9223372036854775807;

    axiom number_product_long_long_bounds:
      \forall integer k;
        1 <= k && k <= 303 ==>
          0 <= k * (k + 1)
          && k * (k + 1) <= 9223372036854775807;
  }
*/

/*@
  requires 0 <= n;
  requires n <= 303;
  assigns \nothing;
  ensures \result == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2;
*/
int DifferenceSumCubesAndSumNumbers(int n)
{
    long long sumCubes = 0;
    long long sumNumbers = 0;
    int i;

    /*@
      loop invariant 0 <= n;
      loop invariant n <= 303;
      loop invariant 1 <= i;
      loop invariant i <= n + 1;
      loop invariant i <= 304;
      loop invariant sumCubes == ((i - 1) * (i - 1) * i * i) / 4;
      loop invariant sumNumbers == ((i - 1) * i) / 2;
      loop invariant 0 <= sumCubes;
      loop invariant sumCubes <= 2147483647;
      loop invariant 0 <= sumNumbers;
      loop invariant sumNumbers <= 2147483647;
      loop assigns i, sumCubes, sumNumbers;
      loop variant n + 1 - i;
    */
    for (i = 1; i < n + 1; i++) {
        //@ assert i <= n;
        //@ assert i <= 303;
        //@ assert 1 <= i;
        //@ assert i + 1 <= 304;
        //@ assert 0 <= i * i * (i + 1) * (i + 1);
        //@ assert i * i * (i + 1) * (i + 1) <= 9223372036854775807;

        sumCubes = ((long long)i * (long long)i * (long long)(i + 1) * (long long)(i + 1)) / 4;

        //@ assert sumCubes == (i * i * (i + 1) * (i + 1)) / 4;
        //@ assert 0 <= sumCubes;
        //@ assert sumCubes <= 2147483647;
        //@ assert 0 <= i * (i + 1);
        //@ assert i * (i + 1) <= 9223372036854775807;

        sumNumbers = ((long long)i * (long long)(i + 1)) / 2;

        //@ assert sumNumbers == (i * (i + 1)) / 2;
        //@ assert 0 <= sumNumbers;
        //@ assert sumNumbers <= 2147483647;
    }

    //@ assert i == n + 1;
    //@ assert i - 1 == n;
    //@ assert sumCubes == (n * n * (n + 1) * (n + 1)) / 4;
    //@ assert sumNumbers == (n * (n + 1)) / 2;

    long long diff = sumCubes - sumNumbers;

    //@ assert diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2;
    //@ assert 0 <= (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2;
    //@ assert (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2 <= 2147483647;
    //@ assert 0 <= diff;
    //@ assert diff <= 2147483647;

    return (int)diff;
}