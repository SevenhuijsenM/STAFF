/*@
  predicate InArraySpec{L}(int *a, integer n, integer x) =
    0 <= n && (\exists integer i; 0 <= i && i < n && \at(a[i], L) == x);

  predicate UniquePrefix{L}(int *a, integer n) =
    0 <= n &&
    (\forall integer i, j; 0 <= i && i < j && j < n ==> \at(a[i], L) != \at(a[j], L));
*/

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n-1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result == 1) <==> InArraySpec(a, n, x);
  ensures (\result == 0) <==> ! InArraySpec(a, n, x);
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
    for (; i < n; i++) {
        if (a[i] == x) {
            return 1;
        }
    }

    return 0;
}

/*@
  requires a_len >= 0;
  requires b_len >= 0;
  requires a_len == 0 || \valid_read(a + (0 .. a_len-1));
  requires b_len == 0 || \valid_read(b + (0 .. b_len-1));
  requires a_len == 0 || \valid(result + (0 .. a_len-1));
  requires a_len == 0 || \separated(result + (0 .. a_len-1), a + (0 .. a_len-1));
  requires a_len == 0 || b_len == 0 || \separated(result + (0 .. a_len-1), b + (0 .. b_len-1));
  assigns result[0 .. a_len-1];
  ensures 0 <= \result && \result <= a_len;
  ensures \forall integer k; 0 <= k && k < \result ==> InArraySpec(a, a_len, result[k]) && InArraySpec(b, b_len, result[k]);
  ensures \forall integer i, j; 0 <= i && i < j && j < \result ==> result[i] != result[j];
*/
int Intersection(int *a, int a_len, int *b, int b_len, int *result)
{
    int res_len = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= a_len;
      loop invariant 0 <= res_len && res_len <= i;
      loop invariant \forall integer k; 0 <= k && k < res_len ==> InArraySpec(a, a_len, result[k]) && InArraySpec(b, b_len, result[k]);
      loop invariant \forall integer p, q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];
      loop assigns i, res_len, result[0 .. a_len-1];
      loop variant a_len - i;
    */
    for (; i < a_len; i++) {
        int value = a[i];
        int in_b = InArray(b, b_len, value);

        if (in_b != 0) {
            int in_res;

            //@ assert InArraySpec(b, b_len, value);
            //@ assert 0 <= i && i < a_len;
            //@ assert a[i] == value;
            //@ assert InArraySpec(a, a_len, value);

            in_res = InArray(result, res_len, value);

            if (in_res == 0) {
                int old_res_len = res_len;

                //@ assert ! InArraySpec(result, res_len, value);
                //@ assert \forall integer k; 0 <= k && k < res_len ==> result[k] != value;
                //@ assert old_res_len == res_len;
                //@ assert 0 <= old_res_len && old_res_len <= i;
                //@ assert i < a_len;
                //@ assert old_res_len < a_len;
                //@ assert InArraySpec(a, a_len, value);
                //@ assert InArraySpec(b, b_len, value);
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InArraySpec(a, a_len, result[k]) && InArraySpec(b, b_len, result[k]);
                //@ assert \forall integer p, q; 0 <= p && p < q && q < old_res_len ==> result[p] != result[q];

BeforeStore:
                result[old_res_len] = value;

                //@ assert result[old_res_len] == value;
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] == \at(result[k], BeforeStore);
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != value;
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> result[k] != result[old_res_len];
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InArraySpec(a, a_len, result[k]) && InArraySpec(b, b_len, result[k]);
                //@ assert InArraySpec(a, a_len, result[old_res_len]);
                //@ assert InArraySpec(b, b_len, result[old_res_len]);
                //@ assert \forall integer k; 0 <= k && k <= old_res_len ==> (k < old_res_len || k == old_res_len);
                //@ assert \forall integer k; 0 <= k && k <= old_res_len ==> InArraySpec(a, a_len, result[k]) && InArraySpec(b, b_len, result[k]);
                //@ assert \forall integer p; 0 <= p && p < old_res_len ==> result[p] != result[old_res_len];
                //@ assert \forall integer p, q; 0 <= p && p < q && q < old_res_len ==> result[p] != result[q];
                //@ assert \forall integer p, q; 0 <= p && p < q && q <= old_res_len ==> result[p] != result[q];

                res_len = old_res_len + 1;

                //@ assert res_len == old_res_len + 1;
                //@ assert 0 <= res_len && res_len <= i + 1;
                //@ assert \forall integer k; 0 <= k && k < res_len ==> k <= old_res_len;
                //@ assert \forall integer k; 0 <= k && k < res_len ==> InArraySpec(a, a_len, result[k]) && InArraySpec(b, b_len, result[k]);
                //@ assert \forall integer p, q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];
            }
        }
    }

    return res_len;
}