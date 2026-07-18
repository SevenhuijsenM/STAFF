#include <limits.h>

typedef struct {
    int sum;
    double average;
} SumAndAverageResult;

/*@
  requires n > 0;
  requires n <= 65535;
  requires 2147450880 <= INT_MAX;
  assigns \nothing;
  ensures \result.sum == n * (n + 1) / 2;
  ensures \result.average == (double)(n + 1) / (double)2;
*/
SumAndAverageResult SumAndAverage(int n) {
    int s = 0;
    int i = 1;

    /*@
      loop invariant 1 <= i;
      loop invariant i <= n + 1;
      loop invariant i <= 65536;
      loop invariant s == (i - 1) * i / 2;
      loop invariant 2 * s == (i - 1) * i;
      loop invariant 0 <= s;
      loop invariant s <= INT_MAX;
      loop assigns i, s;
      loop variant n + 1 - i;
    */
    while (i < n + 1) {
        //@ assert i <= n;
        //@ assert i <= 65535;
        //@ assert s == (i - 1) * i / 2;
        //@ assert 2 * s == (i - 1) * i;
        //@ assert s + i == i * (i + 1) / 2;
        //@ assert i * (i + 1) / 2 <= n * (n + 1) / 2;
        //@ assert n * (n + 1) / 2 <= 2147450880;
        //@ assert 2147450880 <= INT_MAX;
        //@ assert s + i <= INT_MAX;
        s = s + i;
        //@ assert s == i * (i + 1) / 2;
        //@ assert 2 * s == i * (i + 1);
        i = i + 1;
    }

    //@ assert i >= n + 1;
    //@ assert i <= n + 1;
    //@ assert i == n + 1;
    //@ assert s == (i - 1) * i / 2;
    //@ assert s == n * (n + 1) / 2;

    SumAndAverageResult result;
    result.sum = s;
    result.average = (double)(n + 1) / (double)2;

    //@ assert result.sum == n * (n + 1) / 2;
    //@ assert result.average == (double)(n + 1) / (double)2;

    return result;
}