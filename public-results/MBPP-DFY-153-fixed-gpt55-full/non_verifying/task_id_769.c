/*@
  axiomatic Array_Logic {
    predicate in_array{L}(integer x, const int *p, integer n) =
      \exists integer k; 0 <= k && k < n && p[k] == x;

    predicate all_distinct{L}(const int *p, integer n) =
      \forall integer i, j; 0 <= i && i < j && j < n ==> p[i] != p[j];

    axiom in_array_empty{L}:
      \forall const int *p, integer x;
        !in_array(x, p, 0);

    axiom in_array_extend{L}:
      \forall const int *p, integer n, integer x;
        0 <= n ==>
          (in_array(x, p, n + 1) <==>
           (in_array(x, p, n) || p[n] == x));

    axiom in_array_monotone_one{L}:
      \forall const int *p, integer n, integer x;
        0 <= n ==>
          (in_array(x, p, n) ==> in_array(x, p, n + 1));

    axiom in_array_last{L}:
      \forall const int *p, integer n;
        0 <= n ==> in_array(p[n], p, n + 1);

    axiom all_distinct_empty{L}:
      \forall const int *p;
        all_distinct(p, 0);

    axiom all_distinct_extend{L}:
      \forall const int *p, integer n;
        0 <= n ==>
          (all_distinct(p, n + 1) <==>
           (all_distinct(p, n) && !in_array(p[n], p, n)));

    axiom all_distinct_shrink{L}:
      \forall const int *p, integer n;
        0 <= n ==>
          (all_distinct(p, n + 1) ==> all_distinct(p, n));
  }
*/

/*@
  requires arr != \null;
  requires 0 <= len;
  requires len == 0 || \valid_read(arr + (0 .. len - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures \result != 0 <==> in_array(x, arr, len);
*/
int contains(const int *arr, int len, int x) {
  int i = 0;

  /*@
    loop invariant 0 <= i;
    loop invariant i <= len;
    loop invariant \forall integer k; 0 <= k && k < i ==> arr[k] != x;
    loop invariant !in_array(x, arr, i);
    loop assigns i;
    loop variant len - i;
  */
  while (i < len) {
    //@ assert 0 <= i;
    //@ assert i < len;
    if (arr[i] == x) {
      //@ assert arr[i] == x;
      //@ assert in_array(x, arr, i + 1);
      //@ assert in_array(x, arr, len);
      return 1;
    }
    //@ assert arr[i] != x;
    i = i + 1;
  }

  //@ assert i == len;
  //@ assert !in_array(x, arr, len);
  return 0;
}

/*@
  requires a != \null;
  requires b != \null;
  requires diff != \null;
  requires diff_len != \null;
  requires 0 <= a_len;
  requires 0 <= b_len;
  requires a_len == 0 || \valid_read(a + (0 .. a_len - 1));
  requires b_len == 0 || \valid_read(b + (0 .. b_len - 1));
  requires a_len == 0 || \valid(diff + (0 .. a_len - 1));
  requires \valid(diff_len);
  requires \separated(a + (0 .. a_len - 1), diff + (0 .. a_len - 1));
  requires \separated(b + (0 .. b_len - 1), diff + (0 .. a_len - 1));
  requires \separated(diff_len, a + (0 .. a_len - 1));
  requires \separated(diff_len, b + (0 .. b_len - 1));
  requires \separated(diff_len, diff + (0 .. a_len - 1));
  assigns diff[0 .. a_len - 1], *diff_len;
  ensures 0 <= *diff_len;
  ensures *diff_len <= a_len;
  ensures \forall integer x;
            in_array(x, diff, *diff_len) <==>
            (in_array(x, a, a_len) && !in_array(x, b, b_len));
  ensures all_distinct(diff, *diff_len);
*/
void Difference(const int *a, int a_len, const int *b, int b_len,
                int *diff, int *diff_len) {
  *diff_len = 0;
  int i = 0;

  //@ assert *diff_len == 0;
  //@ assert all_distinct(diff, *diff_len);
  //@ assert \forall integer x; in_array(x, diff, *diff_len) <==> (in_array(x, a, i) && !in_array(x, b, b_len));

  /*@
    loop invariant 0 <= i;
    loop invariant i <= a_len;
    loop invariant 0 <= *diff_len;
    loop invariant *diff_len <= i;
    loop invariant \forall integer x;
              in_array(x, diff, *diff_len) <==>
              (in_array(x, a, i) && !in_array(x, b, b_len));
    loop invariant all_distinct(diff, *diff_len);
    loop invariant \forall integer k;
              0 <= k && k < *diff_len ==> in_array(diff[k], a, i);
    loop invariant \forall integer k;
              0 <= k && k < *diff_len ==> !in_array(diff[k], b, b_len);
    loop invariant \forall integer k;
              0 <= k && k < i && !in_array(a[k], b, b_len) ==> in_array(a[k], diff, *diff_len);
    loop assigns i, *diff_len, diff[0 .. a_len - 1];
    loop variant a_len - i;
  */
  while (i < a_len) {
    int v = a[i];

    //@ assert 0 <= i;
    //@ assert i < a_len;
    //@ assert \valid_read(a + i);
    //@ assert v == a[i];
    //@ assert in_array(v, a, i + 1);
    //@ assert \forall integer x; in_array(x, a, i + 1) <==> (in_array(x, a, i) || x == v);

    int in_b = contains(b, b_len, v);

    //@ assert in_b == 0 || in_b == 1;
    //@ assert in_b != 0 <==> in_array(v, b, b_len);

    int in_d = contains(diff, *diff_len, v);

    //@ assert in_d == 0 || in_d == 1;
    //@ assert in_d != 0 <==> in_array(v, diff, *diff_len);

    if (in_b == 0 && in_d == 0) {
      int old_len = *diff_len;

      //@ assert 0 <= old_len;
      //@ assert old_len == *diff_len;
      //@ assert old_len <= i;
      //@ assert old_len < a_len;
      //@ assert !in_array(v, b, b_len);
      //@ assert !in_array(v, diff, old_len);
      //@ assert all_distinct(diff, old_len);

      diff[old_len] = v;

      //@ assert diff[old_len] == v;
      //@ assert !in_array(diff[old_len], diff, old_len);

      *diff_len = old_len + 1;

      //@ assert *diff_len == old_len + 1;
      //@ assert in_array(v, diff, *diff_len);
      //@ assert all_distinct(diff, *diff_len);
      //@ assert \forall integer x; in_array(x, diff, *diff_len) <==> (in_array(x, diff, old_len) || x == v);
      //@ assert \forall integer x; in_array(x, diff, old_len) <==> (in_array(x, a, i) && !in_array(x, b, b_len));
      //@ assert \forall integer x; in_array(x, diff, *diff_len) <==> (in_array(x, a, i + 1) && !in_array(x, b, b_len));
      //@ assert \forall integer k; 0 <= k && k < *diff_len ==> in_array(diff[k], a, i + 1);
      //@ assert \forall integer k; 0 <= k && k < *diff_len ==> !in_array(diff[k], b, b_len);
      //@ assert \forall integer k; 0 <= k && k < i + 1 && !in_array(a[k], b, b_len) ==> in_array(a[k], diff, *diff_len);
    } else {
      //@ assert in_b != 0 || in_d != 0;

      if (in_b != 0) {
        //@ assert in_array(v, b, b_len);
        //@ assert \forall integer x; in_array(x, a, i + 1) && !in_array(x, b, b_len) ==> in_array(x, a, i) && !in_array(x, b, b_len);
        //@ assert \forall integer x; in_array(x, diff, *diff_len) <==> (in_array(x, a, i + 1) && !in_array(x, b, b_len));
      } else {
        //@ assert in_d != 0;
        //@ assert in_array(v, diff, *diff_len);
        //@ assert \forall integer x; in_array(x, a, i + 1) && !in_array(x, b, b_len) ==> in_array(x, diff, *diff_len);
        //@ assert \forall integer x; in_array(x, diff, *diff_len) <==> (in_array(x, a, i + 1) && !in_array(x, b, b_len));
      }

      //@ assert all_distinct(diff, *diff_len);
      //@ assert \forall integer k; 0 <= k && k < *diff_len ==> in_array(diff[k], a, i + 1);
      //@ assert \forall integer k; 0 <= k && k < *diff_len ==> !in_array(diff[k], b, b_len);
      //@ assert \forall integer k; 0 <= k && k < i + 1 && !in_array(a[k], b, b_len) ==> in_array(a[k], diff, *diff_len);
      //@ assert \forall integer x; in_array(x, diff, *diff_len) <==> (in_array(x, a, i + 1) && !in_array(x, b, b_len));
    }

    //@ assert i + 1 <= a_len;
    i = i + 1;
  }

  //@ assert i == a_len;
  //@ assert 0 <= *diff_len;
  //@ assert *diff_len <= a_len;
  //@ assert all_distinct(diff, *diff_len);
  //@ assert \forall integer x; in_array(x, diff, *diff_len) <==> (in_array(x, a, a_len) && !in_array(x, b, b_len));
}