#include <limits.h>

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> (48 <= (int)c && (int)c <= 57);
*/
int IsDigit(char c)
{
    return 48 <= (int)c && (int)c <= 57;
}

/*@
  requires n >= 0;
  requires n <= INT_MAX - 9;
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  assigns \nothing;
  ensures \result >= 0;
  ensures \result <= n;
*/
int CountSubstringsWithSumOfDigitsEqualToLength(const char *s, int n)
{
    int count = 0;
    int i;
    int j;
    int sum;
    int digit;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant 0 <= count && count <= i;
      loop assigns i, j, sum, digit, count;
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        sum = 0;

        /*@
          loop invariant i <= j && j <= n;
          loop invariant sum >= 0;
          loop invariant sum <= j - i;
          loop invariant 0 <= count && count <= i;
          loop assigns j, sum, digit, count;
          loop variant n - j;
        */
        for (j = i; j < n; j++) {
            if (j == n || !IsDigit(s[j])) {
                if (sum == j - i) {
                    count = count + 1;
                }
                break;
            }

            digit = (int)s[j] - 48;
            sum = sum + digit;

            if (sum > j - i + 1) {
                break;
            }
        }

        //@ assert 0 <= count;
        //@ assert count <= i + 1;
    }

    return count;
}