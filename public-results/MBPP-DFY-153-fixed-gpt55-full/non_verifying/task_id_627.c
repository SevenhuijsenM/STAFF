/*@
  requires n >= 0;
  requires n == 0 || \valid_read(s + (0 .. n-1));
  requires \forall integer i, j; 0 <= i && i < j && j < n ==> s[i] <= s[j];
  requires \forall integer i; 0 <= i && i < n ==> s[i] >= 0;
  assigns \nothing;
  ensures \result >= 0;
  ensures \result <= n;
  ensures \forall integer i; 0 <= i && i < n ==> s[i] != \result;
  ensures \forall integer k; 0 <= k && k < \result ==> \exists integer i; 0 <= i && i < n && s[i] == k;
*/
int SmallestMissingNumber(const int *s, int n)
{
    int v = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant 0 <= v && v <= i;
      loop invariant \forall integer j; 0 <= j && j < i ==> s[j] < v;
      loop invariant \forall integer k; 0 <= k && k < v ==> \exists integer j; 0 <= j && j < i && s[j] == k;
      loop assigns i, v;
      loop variant n - i;
    */
    while (i < n && s[i] <= v) {
        //@ assert 0 <= i;
        //@ assert i < n;
        //@ assert 0 <= v;
        //@ assert v <= i;
        //@ assert s[i] <= v;

        if (s[i] == v) {
            int old_v = v;
            //@ assert old_v == v;
            //@ assert s[i] == old_v;
            //@ assert old_v <= i;
            //@ assert old_v < n;
            //@ assert \forall integer j; 0 <= j && j < i ==> s[j] < old_v;
            //@ assert \forall integer k; 0 <= k && k < old_v ==> \exists integer j; 0 <= j && j < i && s[j] == k;

            v = v + 1;

            //@ assert v == old_v + 1;
            //@ assert old_v < v;
            //@ assert v <= i + 1;
            //@ assert s[i] < v;
            //@ assert 0 <= i && i < i + 1;
            //@ assert \exists integer j; 0 <= j && j < i + 1 && s[j] == old_v;
            //@ assert \forall integer j; 0 <= j && j < i ==> s[j] < v;
            //@ assert \forall integer j; 0 <= j && j < i + 1 ==> s[j] < v;
            //@ assert \forall integer k; 0 <= k && k < v ==> (k < old_v || k == old_v);
            //@ assert \forall integer k; 0 <= k && k < v && k < old_v ==> \exists integer j; 0 <= j && j < i && s[j] == k;
            //@ assert \forall integer k; 0 <= k && k < v && k < old_v ==> \exists integer j; 0 <= j && j < i + 1 && s[j] == k;
            //@ assert \forall integer k; 0 <= k && k < v && k == old_v ==> \exists integer j; 0 <= j && j < i + 1 && s[j] == k;
            //@ assert \forall integer k; 0 <= k && k < v ==> \exists integer j; 0 <= j && j < i + 1 && s[j] == k;
        } else {
            //@ assert s[i] != v;
            //@ assert s[i] < v;
            //@ assert \forall integer j; 0 <= j && j < i ==> s[j] < v;
            //@ assert \forall integer j; 0 <= j && j < i + 1 ==> s[j] < v;
            //@ assert \forall integer k; 0 <= k && k < v ==> \exists integer j; 0 <= j && j < i && s[j] == k;
            //@ assert \forall integer k; 0 <= k && k < v ==> \exists integer j; 0 <= j && j < i + 1 && s[j] == k;
        }

        //@ assert 0 <= v;
        //@ assert v <= i + 1;
        //@ assert \forall integer j; 0 <= j && j < i + 1 ==> s[j] < v;
        //@ assert \forall integer k; 0 <= k && k < v ==> \exists integer j; 0 <= j && j < i + 1 && s[j] == k;

        i = i + 1;

        //@ assert 0 <= i && i <= n;
        //@ assert 0 <= v && v <= i;
        //@ assert \forall integer j; 0 <= j && j < i ==> s[j] < v;
        //@ assert \forall integer k; 0 <= k && k < v ==> \exists integer j; 0 <= j && j < i && s[j] == k;
    }

    //@ assert 0 <= i && i <= n;
    //@ assert 0 <= v && v <= i;
    //@ assert \forall integer j; 0 <= j && j < i ==> s[j] < v;
    //@ assert \forall integer k; 0 <= k && k < v ==> \exists integer j; 0 <= j && j < i && s[j] == k;

    if (i < n) {
        //@ assert !(i < n && s[i] <= v);
        //@ assert s[i] > v;
        //@ assert \forall integer j; i < j && j < n ==> s[i] <= s[j];
    } else {
        //@ assert i == n;
    }

    int t = 0;

    /*@
      loop invariant 0 <= t && t <= n;
      loop invariant 0 <= i && i <= n;
      loop invariant 0 <= v && v <= i;
      loop invariant \forall integer j; 0 <= j && j < i ==> s[j] < v;
      loop invariant i < n ==> s[i] > v;
      loop invariant i < n ==> \forall integer j; i < j && j < n ==> s[i] <= s[j];
      loop invariant \forall integer j; 0 <= j && j < t ==> s[j] != v;
      loop assigns t;
      loop variant n - t;
    */
    while (t < n) {
        //@ assert 0 <= t;
        //@ assert t < n;

        if (t < i) {
            //@ assert s[t] < v;
            //@ assert s[t] != v;
        } else {
            //@ assert i <= t;
            if (i < n) {
                //@ assert s[i] > v;
                if (t == i) {
                    //@ assert s[t] > v;
                    //@ assert s[t] != v;
                } else {
                    //@ assert i < t;
                    //@ assert t < n;
                    //@ assert s[i] <= s[t];
                    //@ assert s[t] > v;
                    //@ assert s[t] != v;
                }
            } else {
                //@ assert i == n;
                //@ assert t < n;
                //@ assert i <= t;
                //@ assert \false;
            }
        }

        //@ assert s[t] != v;
        //@ assert \forall integer j; 0 <= j && j < t + 1 ==> s[j] != v;

        t = t + 1;

        //@ assert 0 <= t && t <= n;
        //@ assert \forall integer j; 0 <= j && j < t ==> s[j] != v;
    }

    //@ assert \forall integer j; 0 <= j && j < n ==> s[j] != v;

    int k = 0;

    /*@
      loop invariant 0 <= k && k <= v;
      loop invariant 0 <= i && i <= n;
      loop invariant 0 <= v && v <= i;
      loop invariant \forall integer h; 0 <= h && h < v ==> \exists integer j; 0 <= j && j < i && s[j] == h;
      loop invariant \forall integer h; 0 <= h && h < k ==> \exists integer j; 0 <= j && j < n && s[j] == h;
      loop assigns k;
      loop variant v - k;
    */
    while (k < v) {
        //@ assert 0 <= k;
        //@ assert k < v;
        //@ assert \exists integer j; 0 <= j && j < i && s[j] == k;
        //@ assert i <= n;
        //@ assert \exists integer j; 0 <= j && j < n && s[j] == k;
        //@ assert \forall integer h; 0 <= h && h < k + 1 ==> \exists integer j; 0 <= j && j < n && s[j] == h;

        k = k + 1;

        //@ assert 0 <= k && k <= v;
        //@ assert \forall integer h; 0 <= h && h < k ==> \exists integer j; 0 <= j && j < n && s[j] == h;
    }

    //@ assert 0 <= v;
    //@ assert v <= n;
    //@ assert \forall integer j; 0 <= j && j < n ==> s[j] != v;
    //@ assert \forall integer h; 0 <= h && h < v ==> \exists integer j; 0 <= j && j < n && s[j] == h;

    return v;
}