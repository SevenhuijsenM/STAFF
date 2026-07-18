#include <stddef.h>

typedef struct {
    const int *data;
    size_t length;
} IntSeq;

/*@
  requires lists_len > 0;
  requires \valid_read(lists + (0 .. lists_len - 1));
  requires \forall integer k;
            0 <= k && k < lists_len ==>
              (lists[k].length == 0 ||
               \valid_read(lists[k].data + (0 .. lists[k].length - 1)));
  assigns \nothing;
  ensures \forall integer k;
            0 <= k && k < lists_len ==> lists[k].length <= \result.length;
  ensures \exists integer k;
            0 <= k && k < lists_len &&
            \result.length == lists[k].length &&
            \result.data == lists[k].data;
*/
IntSeq MaxLengthList(const IntSeq *lists, size_t lists_len)
{
    IntSeq maxList = lists[0];

    /*@
      loop invariant 1 <= i && i <= lists_len;
      loop invariant \forall integer k;
                        0 <= k && k < i ==> lists[k].length <= maxList.length;
      loop invariant \exists integer k;
                        0 <= k && k < i &&
                        maxList.length == lists[k].length &&
                        maxList.data == lists[k].data;
      loop assigns i, maxList;
      loop variant lists_len - i;
    */
    for (size_t i = 1; i < lists_len; i++) {
        if (lists[i].length > maxList.length) {
            maxList = lists[i];
        }
    }

    return maxList;
}