#include <limits.h>

/*@
  requires 1 <= a;
  requires 1 <= b;
  requires a <= 65535;
  requires b <= 65535;
  assigns \nothing;
  ensures \result >= 0;
  ensures \forall integer d;
            1 <= d && d <= a && d <= b ==>
              (a % d == 0 && b % d == 0 ==> \result >= d);
*/
int SumOfCommonDivisors(int a, int b) {
  int sum = 0;
  int i = 1;

  /*@
    loop invariant 1 <= i;
    loop invariant i <= a + 1;
    loop invariant i <= b + 1;
    loop invariant sum >= 0;
    loop invariant sum <= ((i - 1) * i) / 2;
    loop invariant \forall integer d;
              1 <= d && d < i ==>
                (a % d == 0 && b % d == 0 ==> sum >= d);
    loop assigns sum, i;
    loop variant a - i + 1;
  */
  while (i <= a && i <= b) {
    if (a % i == 0 && b % i == 0) {
      sum = sum + i;
    }
    i = i + 1;
  }

  return sum;
}