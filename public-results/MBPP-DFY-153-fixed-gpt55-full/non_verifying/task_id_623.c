#include <limits.h>

/*@
  axiomatic PowerModelAxioms {
    logic integer PowerModel(integer base, integer exponent);

    axiom PowerModel_zero:
      \forall integer base; PowerModel(base, 0) == 1;

    axiom PowerModel_positive:
      \forall integer base, exponent;
        exponent > 0 ==>
        PowerModel(base, exponent) == base * PowerModel(base, exponent - 1);
  }
*/

typedef struct {
  int *data;
  int length;
} IntSeq;

/*@
  requires exponent >= 0;
  requires \forall integer e;
    0 <= e && e <= exponent ==>
    INT_MIN <= PowerModel(base, e) && PowerModel(base, e) <= INT_MAX;
  assigns \nothing;
  decreases exponent;
  ensures \result == PowerModel(base, exponent);
*/
int Power(int base, int exponent) {
  if (exponent == 0) {
    //@ assert PowerModel(base, 0) == 1;
    return 1;
  } else {
    //@ assert exponent > 0;
    //@ assert exponent - 1 >= 0;
    /*@ assert \forall integer e;
          0 <= e && e <= exponent - 1 ==>
          INT_MIN <= PowerModel(base, e) && PowerModel(base, e) <= INT_MAX;
    */
    int p = Power(base, exponent - 1);
    //@ assert p == PowerModel(base, exponent - 1);
    //@ assert PowerModel(base, exponent) == base * PowerModel(base, exponent - 1);
    //@ assert PowerModel(base, exponent) == base * p;
    //@ assert INT_MIN <= PowerModel(base, exponent);
    //@ assert PowerModel(base, exponent) <= INT_MAX;
    //@ assert INT_MIN <= base * p;
    //@ assert base * p <= INT_MAX;
    long long q = (long long)base * (long long)p;
    //@ assert q == base * p;
    //@ assert q == PowerModel(base, exponent);
    //@ assert INT_MIN <= q;
    //@ assert q <= INT_MAX;
    return (int)q;
  }
}

/*@
  requires n >= 0;
  requires l.length >= 0;
  requires l.length == 0 || \valid_read(l.data + (0 .. l.length - 1));
  requires l.length == 0 || \valid(result_buffer + (0 .. l.length - 1));
  requires l.length == 0 ||
    \separated(l.data + (0 .. l.length - 1),
               result_buffer + (0 .. l.length - 1));
  requires \forall integer i, e;
    0 <= i && i < l.length && 0 <= e && e <= n ==>
    INT_MIN <= PowerModel(l.data[i], e) &&
    PowerModel(l.data[i], e) <= INT_MAX;
  assigns result_buffer[0 .. l.length - 1];
  ensures \result.length == l.length;
  ensures \result.data == result_buffer;
  ensures \forall integer i;
    0 <= i && i < l.length ==>
    \result.data[i] == PowerModel(l.data[i], n);
*/
IntSeq PowerOfListElements(IntSeq l, int n, int *result_buffer) {
  IntSeq result;
  result.data = result_buffer;
  result.length = 0;

  int i = 0;

  /*@
    loop invariant 0 <= i;
    loop invariant i <= l.length;
    loop invariant result.data == result_buffer;
    loop invariant result.length == i;
    loop invariant l.length >= 0;
    loop invariant l.length == 0 || \valid_read(l.data + (0 .. l.length - 1));
    loop invariant l.length == 0 || \valid(result_buffer + (0 .. l.length - 1));
    loop invariant l.length == 0 ||
      \separated(l.data + (0 .. l.length - 1),
                 result_buffer + (0 .. l.length - 1));
    loop invariant \forall integer k;
      0 <= k && k < i ==>
      result.data[k] == PowerModel(l.data[k], n);
    loop invariant \forall integer k, e;
      0 <= k && k < l.length && 0 <= e && e <= n ==>
      INT_MIN <= PowerModel(l.data[k], e) &&
      PowerModel(l.data[k], e) <= INT_MAX;
    loop assigns i, result.length, result.data[0 .. l.length - 1];
    loop variant l.length - i;
  */
  for (i = 0; i < l.length; i++) {
    //@ assert 0 <= i;
    //@ assert i < l.length;
    //@ assert i + 1 <= l.length;
    //@ assert \valid_read(l.data + i);
    //@ assert result.data == result_buffer;
    //@ assert \valid(result.data + i);
    /*@ assert \forall integer e;
          0 <= e && e <= n ==>
          INT_MIN <= PowerModel(l.data[i], e) &&
          PowerModel(l.data[i], e) <= INT_MAX;
    */
    int v = Power(l.data[i], n);
    //@ assert v == PowerModel(l.data[i], n);
    result.data[i] = v;
    //@ assert result.data[i] == PowerModel(l.data[i], n);
    /*@ assert \forall integer k;
          0 <= k && k < i ==>
          result.data[k] == PowerModel(l.data[k], n);
    */
    /*@ assert \forall integer k;
          0 <= k && k < i + 1 ==>
          (k < i || k == i);
    */
    result.length = i + 1;
    //@ assert result.length == i + 1;
    /*@ assert \forall integer k;
          0 <= k && k < result.length ==>
          result.data[k] == PowerModel(l.data[k], n);
    */
  }

  //@ assert i == l.length;
  //@ assert result.length == l.length;
  /*@ assert \forall integer k;
        0 <= k && k < l.length ==>
        result.data[k] == PowerModel(l.data[k], n);
  */
  return result;
}