#include <stddef.h>
#include <stdint.h>

typedef struct {
    int first;
    int second;
} Pair;

typedef struct {
    Pair *data;
    size_t len;
} PairSeq;

/*@
  requires l_len < SIZE_MAX;
  requires \valid(r_data + (0 .. l_len));
  requires l_len == 0 || \valid_read(l + (0 .. l_len - 1));
  requires l_len == 0 || \separated(r_data + (0 .. l_len), l + (0 .. l_len - 1));
  assigns r_data[0 .. l_len];
  ensures \result.data == r_data;
  ensures \result.len == l_len + 1;
  ensures \result.data[\result.len - 1].first == t.first;
  ensures \result.data[\result.len - 1].second == t.second;
  ensures \forall integer i;
            0 <= i && i < (integer)l_len ==>
              \result.data[i].first == \old(l[i].first) &&
              \result.data[i].second == \old(l[i].second);
*/
PairSeq AddTupleToList(const Pair *l, size_t l_len, Pair t, Pair *r_data)
{
    size_t i = 0;

    /*@
      loop invariant 0 <= i && i <= l_len;
      loop invariant \forall integer j;
                0 <= j && j < (integer)i ==>
                  r_data[j].first == l[j].first &&
                  r_data[j].second == l[j].second;
      loop assigns i, r_data[0 .. l_len];
      loop variant (integer)l_len - (integer)i;
    */
    while (i < l_len) {
        r_data[i] = l[i];
        i++;
    }

    r_data[l_len] = t;

    PairSeq r;
    r.data = r_data;
    r.len = l_len + 1;
    return r;
}