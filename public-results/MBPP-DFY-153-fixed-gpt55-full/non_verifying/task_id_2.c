/*@
  predicate InArraySpec{L}(int const *a, integer n, integer x) =
    \exists integer k; 0 <= k && k < n && \at(a[k], L) == x;
*/

/*@
  requires 0 <= n;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result != 0 ==> InArraySpec(a, n, x);
  ensures \result == 0 ==> !InArraySpec(a, n, x);
*/
int InArray(const int *a, int n, int x)
{
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> a[k] != x;
      loop assigns i;
      loop variant n - i;
    */
    while (i < n) {
        if (a[i] == x) {
            //@ assert 0 <= i;
            //@ assert i < n;
            //@ assert a[i] == x;
            //@ assert InArraySpec(a, n, x);
            return 1;
        }

        //@ assert a[i] != x;
        i++;
    }

    //@ assert i == n;
    //@ assert \forall integer k; 0 <= k && k < n ==> a[k] != x;
    //@ assert !InArraySpec(a, n, x);
    return 0;
}

/*@
  requires 0 <= a_len;
  requires 0 <= b_len;
  requires a_len == 0 || \valid_read(a + (0 .. a_len - 1));
  requires b_len == 0 || \valid_read(b + (0 .. b_len - 1));
  requires a_len == 0 || \valid(result + (0 .. a_len - 1));
  requires a_len == 0 || \separated(result + (0 .. a_len - 1), a + (0 .. a_len - 1));
  requires a_len == 0 || b_len == 0 || \separated(result + (0 .. a_len - 1), b + (0 .. b_len - 1));
  assigns result[0 .. a_len - 1];
  ensures 0 <= \result;
  ensures \result <= a_len;
  ensures \forall integer k;
    0 <= k && k < \result ==>
      InArraySpec(a, a_len, result[k]) && InArraySpec(b, b_len, result[k]);
  ensures \forall integer p, q;
    0 <= p && p < q && q < \result ==> result[p] != result[q];
*/
int SharedElements(const int *a, int a_len, const int *b, int b_len, int *result)
{
    int res_len = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i;
      loop invariant i <= a_len;
      loop invariant 0 <= res_len;
      loop invariant res_len <= i;
      loop invariant \forall integer k;
        0 <= k && k < res_len ==> InArraySpec(a, a_len, result[k]);
      loop invariant \forall integer k;
        0 <= k && k < res_len ==> InArraySpec(b, b_len, result[k]);
      loop invariant \forall integer p, q;
        0 <= p && p < q && q < res_len ==> result[p] != result[q];
      loop assigns i, res_len, result[0 .. a_len - 1];
      loop variant a_len - i;
    */
    while (i < a_len) {
        int current = a[i];

        //@ assert 0 <= i;
        //@ assert i < a_len;
        //@ assert current == a[i];
        //@ assert InArraySpec(a, a_len, current);

        int in_b = InArray(b, b_len, current);

        //@ assert current == a[i];
        //@ assert InArraySpec(a, a_len, current);

        if (in_b != 0) {
            //@ assert InArraySpec(b, b_len, current);

            //@ assert 0 <= res_len;
            //@ assert res_len <= i;
            //@ assert res_len <= a_len;
            //@ assert res_len == 0 || \valid_read(result + (0 .. res_len - 1));

            int already = InArray(result, res_len, current);

            if (already == 0) {
                //@ assert !InArraySpec(result, res_len, current);
                //@ assert \forall integer p; 0 <= p && p < res_len ==> result[p] != current;
                //@ assert res_len <= i;
                //@ assert i < a_len;
                //@ assert res_len < a_len;
                //@ assert current == a[i];
                //@ assert InArraySpec(a, a_len, current);
                //@ assert InArraySpec(b, b_len, current);

                int old_res_len = res_len;

                //@ assert old_res_len == res_len;
                //@ assert 0 <= old_res_len;
                //@ assert old_res_len < a_len;
                //@ assert \forall integer p; 0 <= p && p < old_res_len ==> result[p] != current;
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InArraySpec(a, a_len, result[k]);
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InArraySpec(b, b_len, result[k]);
                //@ assert \forall integer p, q; 0 <= p && p < q && q < old_res_len ==> result[p] != result[q];

                result[old_res_len] = current;

                //@ assert result[old_res_len] == current;
                //@ assert InArraySpec(a, a_len, result[old_res_len]);
                //@ assert InArraySpec(b, b_len, result[old_res_len]);
                //@ assert \forall integer p; 0 <= p && p < old_res_len ==> result[p] != current;
                //@ assert \forall integer p; 0 <= p && p < old_res_len ==> result[p] != result[old_res_len];
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InArraySpec(a, a_len, result[k]);
                //@ assert \forall integer k; 0 <= k && k < old_res_len ==> InArraySpec(b, b_len, result[k]);
                //@ assert \forall integer k; 0 <= k && k < old_res_len + 1 ==> InArraySpec(a, a_len, result[k]);
                //@ assert \forall integer k; 0 <= k && k < old_res_len + 1 ==> InArraySpec(b, b_len, result[k]);
                //@ assert \forall integer p, q; 0 <= p && p < q && q < old_res_len + 1 ==> result[p] != result[q];

                res_len = old_res_len + 1;

                //@ assert 0 <= res_len;
                //@ assert res_len <= i + 1;
                //@ assert \forall integer k; 0 <= k && k < res_len ==> InArraySpec(a, a_len, result[k]);
                //@ assert \forall integer k; 0 <= k && k < res_len ==> InArraySpec(b, b_len, result[k]);
                //@ assert \forall integer p, q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];
            }
        }

        //@ assert 0 <= res_len;
        //@ assert res_len <= i + 1;
        //@ assert \forall integer k; 0 <= k && k < res_len ==> InArraySpec(a, a_len, result[k]);
        //@ assert \forall integer k; 0 <= k && k < res_len ==> InArraySpec(b, b_len, result[k]);
        //@ assert \forall integer p, q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];

        i++;

        //@ assert 0 <= i;
        //@ assert i <= a_len;
        //@ assert res_len <= i;
    }

    //@ assert i == a_len;
    //@ assert 0 <= res_len;
    //@ assert res_len <= a_len;
    //@ assert \forall integer k; 0 <= k && k < res_len ==> InArraySpec(a, a_len, result[k]);
    //@ assert \forall integer k; 0 <= k && k < res_len ==> InArraySpec(b, b_len, result[k]);
    //@ assert \forall integer p, q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];

    return res_len;
}