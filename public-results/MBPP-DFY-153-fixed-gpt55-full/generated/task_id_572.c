/*@
  requires len >= 0;
  requires len == 0 || \valid_read(arr + (0 .. len - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result != 0 ==> \exists integer k; 0 <= k && k < len && arr[k] == value;
  ensures \result == 0 ==> \forall integer k; 0 <= k && k < len ==> arr[k] != value;
  ensures (\exists integer k; 0 <= k && k < len && arr[k] == value) ==> \result != 0;
  ensures (\forall integer k; 0 <= k && k < len ==> arr[k] != value) ==> \result == 0;
*/
int contains_prefix(const int *arr, int len, int value)
{
    int k;

    /*@
      loop invariant 0 <= k && k <= len;
      loop invariant \forall integer j; 0 <= j && j < k ==> arr[j] != value;
      loop assigns k;
      loop variant len - k;
    */
    for (k = 0; k < len; k++) {
        if (arr[k] == value) {
            return 1;
        }
    }

    return 0;
}

/*@
  requires n >= 0;
  requires n == 0 || \valid_read(a + (0 .. n - 1));
  requires n == 0 || \valid(result + (0 .. n - 1));
  requires n == 0 || \separated(a + (0 .. n - 1), result + (0 .. n - 1));
  assigns result[0 .. n - 1];
  ensures 0 <= \result && \result <= n;
  ensures \forall integer r;
            0 <= r && r < \result ==>
              \exists integer k; 0 <= k && k < n && result[r] == a[k];
  ensures \forall integer k;
            0 <= k && k < n ==>
              \exists integer r; 0 <= r && r < \result && result[r] == a[k];
  ensures \forall integer p;
            \forall integer q;
              0 <= p && p < q && q < \result ==> result[p] != result[q];
*/
int RemoveDuplicates(const int *a, int n, int *result)
{
    int res_len = 0;
    int i;
    int present = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant 0 <= res_len && res_len <= i;
      loop invariant \forall integer r;
                0 <= r && r < res_len ==>
                  \exists integer k; 0 <= k && k < i && result[r] == a[k];
      loop invariant \forall integer k;
                0 <= k && k < i ==>
                  \exists integer r; 0 <= r && r < res_len && result[r] == a[k];
      loop invariant \forall integer p;
                \forall integer q;
                  0 <= p && p < q && q < res_len ==> result[p] != result[q];
      loop assigns i, res_len, present, result[0 .. n - 1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        //@ assert 0 <= res_len && res_len <= n;
        //@ assert res_len == 0 || \valid_read(result + (0 .. res_len - 1));
        present = contains_prefix(result, res_len, a[i]);

        if (present == 0) {
            //@ assert \forall integer r; 0 <= r && r < res_len ==> result[r] != a[i];

            result[res_len] = a[i];

            //@ assert result[res_len] == a[i];
            //@ assert \forall integer r; 0 <= r && r < res_len ==> result[r] != result[res_len];
            //@ assert \forall integer r; 0 <= r && r < res_len + 1 ==> \exists integer k; 0 <= k && k < i + 1 && result[r] == a[k];
            //@ assert \forall integer k; 0 <= k && k < i + 1 ==> \exists integer r; 0 <= r && r < res_len + 1 && result[r] == a[k];
            //@ assert \forall integer p; \forall integer q; 0 <= p && p < q && q < res_len + 1 ==> result[p] != result[q];

            res_len++;

            //@ assert \forall integer r; 0 <= r && r < res_len ==> \exists integer k; 0 <= k && k < i + 1 && result[r] == a[k];
            //@ assert \forall integer k; 0 <= k && k < i + 1 ==> \exists integer r; 0 <= r && r < res_len && result[r] == a[k];
            //@ assert \forall integer p; \forall integer q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];
        } else {
            //@ assert present != 0;
            //@ assert \exists integer r; 0 <= r && r < res_len && result[r] == a[i];
            //@ assert \forall integer r; 0 <= r && r < res_len ==> \exists integer k; 0 <= k && k < i + 1 && result[r] == a[k];
            //@ assert \forall integer k; 0 <= k && k < i + 1 ==> \exists integer r; 0 <= r && r < res_len && result[r] == a[k];
            //@ assert \forall integer p; \forall integer q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];
        }

        //@ assert 0 <= res_len && res_len <= i + 1;
        //@ assert \forall integer r; 0 <= r && r < res_len ==> \exists integer k; 0 <= k && k < i + 1 && result[r] == a[k];
        //@ assert \forall integer k; 0 <= k && k < i + 1 ==> \exists integer r; 0 <= r && r < res_len && result[r] == a[k];
        //@ assert \forall integer p; \forall integer q; 0 <= p && p < q && q < res_len ==> result[p] != result[q];
    }

    return res_len;
}