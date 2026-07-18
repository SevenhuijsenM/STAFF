#include <limits.h>

/*@
  predicate InArrayPred{L}(int *a, integer n, integer x) =
    \exists integer i; 0 <= i && i < n && \at(a[i], L) == x;
*/

/*@
  predicate InSymmetricDifference{L}(int *a, integer a_len,
                                     int *b, integer b_len,
                                     integer x) =
    (InArrayPred{L}(a, a_len, x) && !InArrayPred{L}(b, b_len, x)) ||
    (!InArrayPred{L}(a, a_len, x) && InArrayPred{L}(b, b_len, x));
*/

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n-1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result != 0 <==> InArrayPred(a, n, x);
  ensures \result == 0 ==> \forall integer k; 0 <= k && k < n ==> a[k] != x;
  ensures \result != 0 ==> \exists integer k; 0 <= k && k < n && a[k] == x;
*/
int InArray(int *a, int n, int x)
{
    int i;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> a[k] != x;
      loop assigns i;
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        if (a[i] == x) {
            return 1;
        }
    }

    return 0;
}

/*@
  requires a_len >= 0;
  requires b_len >= 0;
  requires result_capacity >= 0;
  requires a_len <= INT_MAX - b_len;
  requires result_capacity >= a_len + b_len;
  requires a_len == 0 || \valid_read(a + (0 .. a_len-1));
  requires b_len == 0 || \valid_read(b + (0 .. b_len-1));
  requires result_capacity == 0 || \valid(result + (0 .. result_capacity-1));
  requires result_capacity == 0 || a_len == 0 ||
           \separated(result + (0 .. result_capacity-1), a + (0 .. a_len-1));
  requires result_capacity == 0 || b_len == 0 ||
           \separated(result + (0 .. result_capacity-1), b + (0 .. b_len-1));
  assigns result[0 .. result_capacity-1];
  ensures 0 <= \result && \result <= a_len + b_len;
  ensures \result <= result_capacity;
  ensures \forall integer x;
            InArrayPred(result, \result, x) ==>
            InSymmetricDifference(a, a_len, b, b_len, x);
  ensures \forall integer i, j;
            0 <= i && i < j && j < \result ==> result[i] != result[j];
*/
int DissimilarElements(int *a, int a_len,
                       int *b, int b_len,
                       int *result, int result_capacity)
{
    int res_len = 0;
    int i;

    /*@
      loop invariant 0 <= i && i <= a_len;
      loop invariant 0 <= res_len && res_len <= i;
      loop invariant res_len <= result_capacity;
      loop invariant \forall integer x;
        InArrayPred(result, res_len, x) ==> InArrayPred(a, a_len, x);
      loop invariant \forall integer x;
        InArrayPred(result, res_len, x) ==>
        InSymmetricDifference(a, a_len, b, b_len, x);
      loop invariant \forall integer p, q;
        0 <= p && p < q && q < res_len ==> result[p] != result[q];
      loop assigns i, res_len, result[0 .. result_capacity-1];
      loop variant a_len - i;
    */
    for (i = 0; i < a_len; i++) {
        int v = a[i];

        //@ assert 0 <= i && i < a_len;
        //@ assert InArrayPred(a, a_len, v);

        if (!InArray(b, b_len, v) && !InArray(result, res_len, v)) {
            int old_res_len = res_len;

            //@ assert !InArrayPred(b, b_len, v);
            //@ assert !InArrayPred(result, old_res_len, v);
            //@ assert InSymmetricDifference(a, a_len, b, b_len, v);
            //@ assert old_res_len == res_len;
            //@ assert res_len < result_capacity;
            //@ assert 0 <= old_res_len && old_res_len < result_capacity;
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> k != old_res_len;
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> \separated(result + k, result + old_res_len);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != v;

            result[old_res_len] = v;

            //@ assert result[old_res_len] == v;
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != result[old_res_len];
            //@ assert InArrayPred(a, a_len, result[old_res_len]);
            //@ assert InSymmetricDifference(a, a_len, b, b_len, result[old_res_len]);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != result[old_res_len];

            res_len = old_res_len + 1;

            //@ assert 0 <= old_res_len && old_res_len < res_len;
            //@ assert InArrayPred(result, res_len, v);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; k == old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; 0 <= k && k < res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
        }
    }

    int partialSize = res_len;

    //@ assert 0 <= partialSize && partialSize <= a_len;
    //@ assert partialSize <= result_capacity;

    /*@
      loop invariant 0 <= i && i <= b_len;
      loop invariant 0 <= partialSize && partialSize <= a_len;
      loop invariant partialSize <= res_len;
      loop invariant res_len <= partialSize + i;
      loop invariant res_len <= result_capacity;
      loop invariant \forall integer k;
        partialSize <= k && k < res_len ==> InArrayPred(b, b_len, result[k]);
      loop invariant \forall integer k;
        0 <= k && k < res_len ==>
        InSymmetricDifference(a, a_len, b, b_len, result[k]);
      loop invariant \forall integer p, q;
        0 <= p && p < q && q < res_len ==> result[p] != result[q];
      loop assigns i, res_len, result[0 .. result_capacity-1];
      loop variant b_len - i;
    */
    for (i = 0; i < b_len; i++) {
        int v = b[i];

        //@ assert 0 <= i && i < b_len;
        //@ assert InArrayPred(b, b_len, v);

        if (!InArray(a, a_len, v) && !InArray(result, res_len, v)) {
            int old_res_len = res_len;

            //@ assert !InArrayPred(a, a_len, v);
            //@ assert !InArrayPred(result, old_res_len, v);
            //@ assert InSymmetricDifference(a, a_len, b, b_len, v);
            //@ assert old_res_len == res_len;
            //@ assert res_len < result_capacity;
            //@ assert 0 <= old_res_len && old_res_len < result_capacity;
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> k != old_res_len;
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> \separated(result + k, result + old_res_len);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != v;

            result[old_res_len] = v;

            //@ assert result[old_res_len] == v;
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != result[old_res_len];
            //@ assert InArrayPred(b, b_len, result[old_res_len]);
            //@ assert InSymmetricDifference(a, a_len, b, b_len, result[old_res_len]);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != result[old_res_len];

            res_len = old_res_len + 1;

            //@ assert 0 <= old_res_len && old_res_len < res_len;
            //@ assert InArrayPred(result, res_len, v);
            //@ assert \forall integer k; partialSize <= k && k < old_res_len ==> InArrayPred(b, b_len, result[k]);
            //@ assert \forall integer k; k == old_res_len ==> InArrayPred(b, b_len, result[k]);
            //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; k == old_res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
            //@ assert \forall integer k; 0 <= k && k < res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
        }
    }

    //@ assert \forall integer k; 0 <= k && k < res_len ==> InSymmetricDifference(a, a_len, b, b_len, result[k]);
    //@ assert \forall integer x; InArrayPred(result, res_len, x) ==> InSymmetricDifference(a, a_len, b, b_len, x);

    return res_len;
}