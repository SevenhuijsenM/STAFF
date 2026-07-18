/*@
  requires n > 0;
  requires \valid_read(lengths + (0 .. n - 1));
  requires \forall integer k; 0 <= k && k < n ==> lengths[k] >= 0;
  assigns \nothing;
  ensures \forall integer i; 0 <= i && i < n ==> \result <= lengths[i];
  ensures \exists integer i; 0 <= i && i < n && \result == lengths[i];
*/
int SmallestListLength(const int *lengths, int n)
{
    int v = lengths[0];

    /*@
      loop invariant 1 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k && k < i ==> v <= lengths[k];
      loop invariant \exists integer k; 0 <= k && k < i && v == lengths[k];
      loop assigns i, v;
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (lengths[i] < v) {
            v = lengths[i];
        }
    }

    return v;
}