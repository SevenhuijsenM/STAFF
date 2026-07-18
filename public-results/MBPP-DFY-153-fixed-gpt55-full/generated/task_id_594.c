#include <limits.h>

/*@ predicate Even(integer n) = n % 2 == 0; */
/*@ predicate Odd(integer n) = n % 2 != 0; */

/*@ lemma odd_not_even:
      \forall integer n; Odd(n) <==> !Even(n);
*/

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result != 0 <==> Even(n);
*/
int IsEven(int n)
{
    return (n % 2) == 0;
}

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result != 0 <==> Odd(n);
*/
int IsOdd(int n)
{
    return (n % 2) != 0;
}

/*@
  requires length >= 2;
  requires \valid_read(a + (0 .. length - 1));
  requires \exists integer i; 0 <= i && i < length && Even(a[i]);
  requires \exists integer i; 0 <= i && i < length && Odd(a[i]);
  requires \forall integer i, j;
            0 <= i && i < length && 0 <= j && j < length ==>
            INT_MIN <= a[i] - a[j] && a[i] - a[j] <= INT_MAX;
  assigns \nothing;
  ensures \exists integer i, j;
            0 <= i && i < length &&
            0 <= j && j < length &&
            Even(a[i]) &&
            Odd(a[j]) &&
            \result == a[i] - a[j] &&
            (\forall integer k; 0 <= k && k < i ==> Odd(a[k])) &&
            (\forall integer k; 0 <= k && k < j ==> Even(a[k]));
*/
int FirstEvenOddDifference(const int *a, int length)
{
    int firstEven = -1;
    int firstOdd = -1;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= length;
      loop invariant firstEven == -1 || (0 <= firstEven && firstEven < i && Even(a[firstEven]));
      loop invariant firstOdd == -1 || (0 <= firstOdd && firstOdd < i && Odd(a[firstOdd]));
      loop invariant firstEven == -1 ==> (\forall integer k; 0 <= k && k < i ==> !Even(a[k]));
      loop invariant firstOdd == -1 ==> (\forall integer k; 0 <= k && k < i ==> !Odd(a[k]));
      loop invariant firstEven != -1 ==> (\forall integer k; 0 <= k && k < firstEven ==> Odd(a[k]));
      loop invariant firstOdd != -1 ==> (\forall integer k; 0 <= k && k < firstOdd ==> Even(a[k]));
      loop assigns i, firstEven, firstOdd;
      loop variant length - i;
    */
    while (i < length && (firstEven == -1 || firstOdd == -1)) {
        if (firstEven == -1 && IsEven(a[i])) {
            firstEven = i;
        }

        if (firstOdd == -1 && IsOdd(a[i])) {
            firstOdd = i;
        }

        i++;
    }

    //@ assert firstEven != -1;
    //@ assert firstOdd != -1;
    //@ assert 0 <= firstEven && firstEven < length;
    //@ assert 0 <= firstOdd && firstOdd < length;
    return a[firstEven] - a[firstOdd];
}