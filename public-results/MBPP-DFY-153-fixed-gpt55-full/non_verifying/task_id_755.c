/*@
  axiomatic MinValue {
    logic integer min_value{L}(int *a, integer n) reads a[0 .. n-1];

    axiom min_value_lower{L}:
      \forall int *a, integer n, integer i;
        n >= 1 &&
        \valid_read{L}(a + (0 .. n-1)) &&
        0 <= i &&
        i < n
        ==> min_value{L}(a, n) <= \at(a[i], L);

    axiom min_value_occurs{L}:
      \forall int *a, integer n;
        n >= 1 &&
        \valid_read{L}(a + (0 .. n-1))
        ==> \exists integer i;
              0 <= i &&
              i < n &&
              min_value{L}(a, n) == \at(a[i], L);

    axiom min_value_at_index{L}:
      \forall int *a, integer n, integer idx;
        n >= 1 &&
        \valid_read{L}(a + (0 .. n-1)) &&
        0 <= idx &&
        idx < n &&
        (\forall integer k;
           0 <= k && k < n ==> \at(a[idx], L) <= \at(a[k], L))
        ==> min_value{L}(a, n) == \at(a[idx], L);

    axiom min_value_pair{L}:
      \forall int *a;
        \valid_read{L}(a + (0 .. 1))
        ==> min_value{L}(a, 2) ==
            (\at(a[0], L) <= \at(a[1], L)
             ? \at(a[0], L)
             : \at(a[1], L));

    axiom min_value_recursive{L}:
      \forall int *a, integer n;
        n > 2 &&
        \valid_read{L}(a + (0 .. n-1))
        ==> min_value{L}(a, n) ==
            (\at(a[0], L) <= min_value{L}(a + 1, n - 1)
             ? \at(a[0], L)
             : min_value{L}(a + 1, n - 1));
  }
*/

/*@
  requires \valid_read(s + (0 .. 1));
  assigns \nothing;
  ensures (s[0] <= s[1]) <==> (\result == s[0]);
  ensures s[0] > s[1] ==> \result == s[1];
  ensures \result <= s[0];
  ensures \result <= s[1];
  ensures \result == s[0] || \result == s[1];
  ensures \result == min_value(s, 2);
*/
int MinPair(int *s)
{
    if (s[0] <= s[1]) {
        return s[0];
    } else {
        return s[1];
    }
}

/*@
  requires n >= 2;
  requires \valid_read(s + (0 .. n-1));
  assigns \nothing;
  decreases n;
  ensures \forall integer i;
            0 <= i && i < n ==> \result <= s[i];
  ensures \result == min_value(s, n);
  ensures \exists integer i;
            0 <= i && i < n && \result == s[i];
*/
int min(int *s, int n)
{
    if (n == 2) {
        int r = MinPair(s);
        //@ assert r == min_value(s, 2);
        return r;
    } else {
        //@ assert n > 2;
        //@ assert n - 1 >= 2;
        //@ assert \valid_read((s + 1) + (0 .. n-2));
        int tail_min = min(s + 1, n - 1);
        //@ assert tail_min == min_value(s + 1, n - 1);
        //@ assert \forall integer j; 0 <= j && j < n - 1 ==> tail_min <= (s + 1)[j];
        //@ assert min_value(s, n) == (s[0] <= min_value(s + 1, n - 1) ? s[0] : min_value(s + 1, n - 1));
        if (s[0] <= tail_min) {
            //@ assert s[0] <= min_value(s + 1, n - 1);
            //@ assert min_value(s, n) == s[0];
            //@ assert \forall integer j; 0 <= j && j < n - 1 ==> s[0] <= (s + 1)[j];
            //@ assert \forall integer i; 0 <= i && i < n ==> s[0] <= s[i];
            return s[0];
        } else {
            //@ assert tail_min < s[0];
            //@ assert min_value(s, n) == tail_min;
            //@ assert \forall integer i; 0 <= i && i < n ==> tail_min <= s[i];
            return tail_min;
        }
    }
}

/*@
  requires n >= 2;
  requires \valid_read(s + (0 .. n-1));
  requires \exists integer i, j;
            0 <= i && i < n &&
            0 <= j && j < n &&
            i != j &&
            s[i] == min_value(s, n) &&
            s[j] != s[i];
  assigns \nothing;
  ensures \exists integer i, j;
            0 <= i && i < n &&
            0 <= j && j < n &&
            i != j &&
            s[i] == min_value(s, n) &&
            s[j] == \result;
  ensures \forall integer k;
            0 <= k && k < n && s[k] != min_value(s, n) ==> s[k] >= \result;
*/
int SecondSmallest(int *s, int n)
{
    int minIndex = 0;
    int secondMinIndex = 1;

    if (s[1] < s[0]) {
        minIndex = 1;
        secondMinIndex = 0;
    }

    //@ assert 0 <= minIndex && minIndex < 2;
    //@ assert 0 <= secondMinIndex && secondMinIndex < 2;
    //@ assert minIndex != secondMinIndex;
    //@ assert s[minIndex] <= s[secondMinIndex];
    //@ assert \forall integer k; 0 <= k && k < 2 ==> s[minIndex] <= s[k];
    //@ assert \forall integer k; 0 <= k && k < 2 && k != minIndex ==> s[secondMinIndex] <= s[k];

    int i;

    /*@
      loop invariant \valid_read(s + (0 .. n-1));
      loop invariant 2 <= i && i <= n;
      loop invariant 0 <= minIndex && minIndex < i;
      loop invariant 0 <= secondMinIndex && secondMinIndex < i;
      loop invariant minIndex != secondMinIndex;
      loop invariant s[minIndex] <= s[secondMinIndex];
      loop invariant \forall integer k;
                        0 <= k && k < i ==> s[minIndex] <= s[k];
      loop invariant \forall integer k;
                        0 <= k && k < i && k != minIndex ==> s[secondMinIndex] <= s[k];
      loop assigns i, minIndex, secondMinIndex;
      loop variant n - i;
    */
    for (i = 2; i < n; i++) {
        //@ assert 0 <= i && i < n;
        //@ assert \forall integer k; 0 <= k && k < i ==> s[minIndex] <= s[k];
        //@ assert \forall integer k; 0 <= k && k < i && k != minIndex ==> s[secondMinIndex] <= s[k];

        if (s[i] < s[minIndex]) {
            //@ assert s[i] < s[minIndex];
            //@ assert \forall integer k; 0 <= k && k < i ==> s[minIndex] <= s[k];
            secondMinIndex = minIndex;
            minIndex = i;
            //@ assert s[minIndex] <= s[secondMinIndex];
            //@ assert \forall integer k; 0 <= k && k < i ==> s[secondMinIndex] <= s[k];
            //@ assert \forall integer k; 0 <= k && k < i + 1 ==> s[minIndex] <= s[k];
            //@ assert \forall integer k; 0 <= k && k < i + 1 && k != minIndex ==> s[secondMinIndex] <= s[k];
        } else {
            //@ assert s[minIndex] <= s[i];
            if (s[i] < s[secondMinIndex]) {
                //@ assert s[i] < s[secondMinIndex];
                //@ assert \forall integer k; 0 <= k && k < i && k != minIndex ==> s[i] <= s[k];
                secondMinIndex = i;
                //@ assert s[minIndex] <= s[secondMinIndex];
                //@ assert \forall integer k; 0 <= k && k < i + 1 ==> s[minIndex] <= s[k];
                //@ assert \forall integer k; 0 <= k && k < i + 1 && k != minIndex ==> s[secondMinIndex] <= s[k];
            } else {
                //@ assert s[secondMinIndex] <= s[i];
                //@ assert \forall integer k; 0 <= k && k < i + 1 ==> s[minIndex] <= s[k];
                //@ assert \forall integer k; 0 <= k && k < i + 1 && k != minIndex ==> s[secondMinIndex] <= s[k];
            }
        }
    }

    //@ assert i == n;
    //@ assert 0 <= minIndex && minIndex < n;
    //@ assert 0 <= secondMinIndex && secondMinIndex < n;
    //@ assert minIndex != secondMinIndex;
    //@ assert \forall integer k; 0 <= k && k < n ==> s[minIndex] <= s[k];
    //@ assert min_value(s, n) == s[minIndex];
    //@ assert s[minIndex] == min_value(s, n);
    //@ assert \forall integer k; 0 <= k && k < n && s[k] != min_value(s, n) ==> k != minIndex;
    //@ assert \forall integer k; 0 <= k && k < n && s[k] != min_value(s, n) ==> s[secondMinIndex] <= s[k];
    //@ assert \exists integer ii, jj; 0 <= ii && ii < n && 0 <= jj && jj < n && ii != jj && s[ii] == min_value(s, n) && s[jj] == s[secondMinIndex];

    return s[secondMinIndex];
}