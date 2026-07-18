#include <limits.h>

/*@
  axiomatic SumTo {
    logic integer sumTo_logic{L}(int *a, integer start, integer end)
      reads a[start .. end - 1];

    axiom sumTo_empty{L}:
      \forall int *a, integer start;
        sumTo_logic{L}(a, start, start) == 0;

    axiom sumTo_step{L}:
      \forall int *a, integer start, integer end;
        0 <= start && start < end &&
        \valid_read(a + (start .. end - 1)) ==>
        sumTo_logic{L}(a, start, end) ==
        sumTo_logic{L}(a, start, end - 1) + a[end - 1];
  }
*/

/*@
  predicate sumTo_fits{L}(int *a, integer start, integer end) =
    \forall integer k;
      start <= k && k <= end ==>
        INT_MIN <= sumTo_logic{L}(a, start, k) &&
        sumTo_logic{L}(a, start, k) <= INT_MAX;
*/

/*@
  requires 0 <= a_length;
  requires 0 <= start;
  requires start <= end;
  requires end <= a_length;
  requires a_length == 0 || \valid_read(a + (0 .. a_length - 1));
  requires sumTo_fits(a, start, end);
  assigns \nothing;
  ensures \result == sumTo_logic(a, start, end);
  ensures INT_MIN <= \result;
  ensures \result <= INT_MAX;
*/
int sumTo(int *a, int a_length, int start, int end) {
  if (start == end) {
    //@ assert sumTo_logic(a, start, start) == 0;
    return 0;
  } else {
    //@ assert start < end;
    //@ assert 0 <= start;
    //@ assert 0 < end;
    //@ assert end <= a_length;
    //@ assert 0 < a_length;
    //@ assert end - 1 < a_length;
    //@ assert 0 <= end - 1;
    //@ assert start <= end - 1;
    //@ assert end - 1 <= a_length;
    //@ assert \valid_read(a + (0 .. a_length - 1));
    //@ assert \valid_read(a + (end - 1));
    //@ assert \valid_read(a + (start .. end - 1));
    //@ assert sumTo_fits(a, start, end - 1);
    int previous = sumTo(a, a_length, start, end - 1);
    //@ assert previous == sumTo_logic(a, start, end - 1);
    //@ assert sumTo_logic(a, start, end) == sumTo_logic(a, start, end - 1) + a[end - 1];
    //@ assert sumTo_logic(a, start, end) == previous + a[end - 1];
    //@ assert INT_MIN <= sumTo_logic(a, start, end);
    //@ assert sumTo_logic(a, start, end) <= INT_MAX;
    //@ assert INT_MIN <= previous + a[end - 1];
    //@ assert previous + a[end - 1] <= INT_MAX;
    return previous + a[end - 1];
  }
}

/*@
  requires 0 <= a_length;
  requires 0 <= start;
  requires start <= end;
  requires end <= a_length;
  requires a_length == 0 || \valid_read(a + (0 .. a_length - 1));
  requires sumTo_fits(a, start, end);
  assigns \nothing;
  ensures \result == sumTo_logic(a, start, end);
  ensures INT_MIN <= \result;
  ensures \result <= INT_MAX;
*/
int SumInRange(int *a, int a_length, int start, int end) {
  int sum = 0;
  int i = start;

  //@ assert sumTo_logic(a, start, start) == 0;
  //@ assert i == start;
  //@ assert sum == sumTo_logic(a, start, i);

  /*@
    loop invariant start <= i;
    loop invariant i <= end;
    loop invariant sum == sumTo_logic(a, start, i);
    loop invariant sumTo_fits(a, start, end);
    loop invariant a_length == 0 || \valid_read(a + (0 .. a_length - 1));
    loop assigns i, sum;
    loop variant end - i;
  */
  while (i < end) {
    //@ assert start <= i;
    //@ assert i < end;
    //@ assert end <= a_length;
    //@ assert i < a_length;
    //@ assert 0 <= start;
    //@ assert 0 <= i;
    //@ assert 0 < a_length;
    //@ assert \valid_read(a + (0 .. a_length - 1));
    //@ assert \valid_read(a + i);
    //@ assert \valid_read(a + (start .. i));
    //@ assert start < i + 1;
    //@ assert i + 1 <= end;
    //@ assert sumTo_logic(a, start, i + 1) == sumTo_logic(a, start, i) + a[i];
    //@ assert sumTo_logic(a, start, i + 1) == sum + a[i];
    //@ assert INT_MIN <= sumTo_logic(a, start, i + 1);
    //@ assert sumTo_logic(a, start, i + 1) <= INT_MAX;
    //@ assert INT_MIN <= sum + a[i];
    //@ assert sum + a[i] <= INT_MAX;
    sum = sum + a[i];
    //@ assert sum == sumTo_logic(a, start, i + 1);
    //@ assert i < INT_MAX;
    i = i + 1;
    //@ assert sum == sumTo_logic(a, start, i);
  }

  //@ assert i == end;
  //@ assert sum == sumTo_logic(a, start, end);
  return sum;
}