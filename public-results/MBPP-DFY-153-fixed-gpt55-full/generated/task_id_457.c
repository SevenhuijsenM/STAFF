#include <stddef.h>

typedef struct {
  const int *data;
  size_t length;
} IntSeq;

/*@
  requires s_len > 0;
  requires \valid_read(s + (0 .. s_len - 1));
  requires \forall integer j;
            0 <= j && j < s_len && s[j].length > 0 ==>
              \valid_read(s[j].data + (0 .. s[j].length - 1));
  assigns \nothing;
  ensures \exists integer k;
            0 <= k && k < s_len &&
            \result.data == s[k].data &&
            \result.length == s[k].length;
  ensures \forall integer k;
            0 <= k && k < s_len ==> \result.length <= s[k].length;
*/
IntSeq MinLengthSublist(const IntSeq *s, size_t s_len) {
  IntSeq minSublist = s[0];
  size_t i = 1;

  /*@
    loop invariant 1 <= i && i <= s_len;
    loop invariant \exists integer k;
                    0 <= k && k < i &&
                    minSublist.data == s[k].data &&
                    minSublist.length == s[k].length;
    loop invariant \forall integer k;
                    0 <= k && k < i ==> minSublist.length <= s[k].length;
    loop assigns i, minSublist;
    loop variant s_len - i;
  */
  for (; i < s_len; i++) {
    if (s[i].length < minSublist.length) {
      minSublist = s[i];
    }
  }

  return minSublist;
}