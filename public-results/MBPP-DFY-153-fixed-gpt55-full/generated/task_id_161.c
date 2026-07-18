/*@
  predicate InArray_pred{L}(int *a, integer n, integer x) =
    \exists integer i; 0 <= i && i < n && \at(a[i], L) == x;
*/

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result == 1 <==> InArray_pred(a, n, x);
*/
int InArray(int *a, int n, int x)
{
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> a[k] != x;
      loop assigns i;
      loop variant n - i;
    */
    while (i < n) {
        if (a[i] == x) {
            return 1;
        }
        i++;
    }

    return 0;
}

/*@
  requires a_len >= 0;
  requires b_len >= 0;
  requires a_len == 0 || \valid_read(a + (0 .. a_len - 1));
  requires b_len == 0 || \valid_read(b + (0 .. b_len - 1));
  requires a_len == 0 || \valid(result + (0 .. a_len - 1));
  requires a_len == 0 || \separated(result + (0 .. a_len - 1), a + (0 .. a_len - 1));
  requires a_len == 0 || b_len == 0 || \separated(result + (0 .. a_len - 1), b + (0 .. b_len - 1));
  assigns result[0 .. a_len - 1];
  ensures 0 <= \result && \result <= a_len;
  ensures \forall integer k; 0 <= k && k < \result ==> InArray_pred(a, a_len, result[k]) && !InArray_pred(b, b_len, result[k]);
  ensures \forall integer i, j; 0 <= i && i < j && j < \result ==> result[i] != result[j];
*/
int RemoveElements(int *a, int a_len, int *b, int b_len, int *result)
{
    int res_len = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= a_len;
      loop invariant 0 <= res_len && res_len <= i;
      loop invariant \forall integer k; 0 <= k && k < res_len ==> InArray_pred(a, a_len, result[k]) && !InArray_pred(b, b_len, result[k]);
      loop invariant \forall integer p, q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];
      loop assigns i, res_len, result[0 .. a_len - 1];
      loop variant a_len - i;
    */
    while (i < a_len) {
        if (!InArray(b, b_len, a[i]) && !InArray(result, res_len, a[i])) {
            result[res_len] = a[i];
            res_len++;
        }
        i++;
    }

    return res_len;
}