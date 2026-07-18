#include <stdbool.h>

typedef struct {
  const int *data;
  int length;
} IntSeq;

/*@
  predicate valid_int_seq{L}(IntSeq s) =
    0 <= s.length &&
    (s.length == 0 || \valid_read(s.data + (0 .. s.length - 1)));
*/

/*@
  predicate int_seq_equal{L}(IntSeq a, IntSeq b) =
    0 <= a.length &&
    0 <= b.length &&
    a.length == b.length &&
    (\forall integer k; 0 <= k && k < a.length ==> a.data[k] == b.data[k]);
*/

/*@
  requires valid_int_seq(a);
  requires valid_int_seq(b);
  assigns \nothing;
  ensures (\result != 0) <==> int_seq_equal(a, b);
*/
bool seq_equal(IntSeq a, IntSeq b)
{
  if (a.length != b.length) {
    return false;
  }

  int i = 0;

  /*@
    loop invariant 0 <= i && i <= a.length;
    loop invariant a.length == b.length;
    loop invariant \forall integer k; 0 <= k && k < i ==> a.data[k] == b.data[k];
    loop assigns i;
    loop variant a.length - i;
  */
  while (i < a.length) {
    if (a.data[i] != b.data[i]) {
      //@ assert 0 <= i && i < a.length;
      //@ assert a.data[i] != b.data[i];
      return false;
    }
    i++;
  }

  //@ assert i == a.length;
  return true;
}

/*@
  requires 0 <= list_len;
  requires list_len == 0 || \valid_read(list + (0 .. list_len - 1));
  requires \forall integer j; 0 <= j && j < list_len ==> valid_int_seq(list[j]);
  requires valid_int_seq(sub);
  assigns \nothing;
  ensures (\result != 0) <==>
          (\exists integer i; 0 <= i && i < list_len && int_seq_equal(sub, list[i]));
*/
bool ContainsSequence(const IntSeq *list, int list_len, IntSeq sub)
{
  int i = 0;

  /*@
    loop invariant 0 <= i && i <= list_len;
    loop invariant \forall integer k; 0 <= k && k < i ==> !int_seq_equal(sub, list[k]);
    loop assigns i;
    loop variant list_len - i;
  */
  while (i < list_len) {
    if (seq_equal(sub, list[i])) {
      //@ assert int_seq_equal(sub, list[i]);
      //@ assert \exists integer k; 0 <= k && k < list_len && int_seq_equal(sub, list[k]);
      return true;
    }

    //@ assert !int_seq_equal(sub, list[i]);
    i++;
  }

  //@ assert i == list_len;
  //@ assert !(\exists integer k; 0 <= k && k < list_len && int_seq_equal(sub, list[k]));
  return false;
}