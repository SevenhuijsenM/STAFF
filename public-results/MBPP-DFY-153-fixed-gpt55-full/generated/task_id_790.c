/*@ predicate IsEvenP(integer n) = n % 2 == 0; */

/*@
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==> IsEvenP(n);
*/
int IsEven(int n)
{
    return (n % 2) == 0;
}

/*@
  requires 0 <= len;
  requires len == 0 || \valid_read(lst + (0 .. len - 1));
  assigns \nothing;
  ensures \result == 0 || \result == 1;
  ensures (\result != 0) <==>
          (\forall integer i;
              0 <= i && i < len ==> (IsEvenP(i) ==> IsEvenP(lst[i])));
*/
int IsEvenAtIndexEven(const int *lst, int len)
{
    int result = 1;
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant result == 0 || result == 1;
      loop invariant (result != 0) <==>
        (\forall integer k;
            0 <= k && k < i ==> (IsEvenP(k) ==> IsEvenP(lst[k])));
      loop invariant result == 0 ==>
        (\exists integer k;
            0 <= k && k < i && IsEvenP(k) && !IsEvenP(lst[k]));
      loop assigns i, result;
      loop variant len - i;
    */
    while (i < len) {
        if (IsEven(i) != 0 && IsEven(lst[i]) == 0) {
            result = 0;
            i = i + 1;
            /*@ assert 0 <= i && i <= len; */
            /*@ assert IsEvenP(i - 1); */
            /*@ assert !IsEvenP(lst[i - 1]); */
            /*@ assert \exists integer k;
                  0 <= k && k < i && IsEvenP(k) && !IsEvenP(lst[k]); */
            break;
        }
        i = i + 1;
    }

    if (result != 0) {
        /*@ assert i == len; */
        /*@ assert \forall integer k;
              0 <= k && k < len ==> (IsEvenP(k) ==> IsEvenP(lst[k])); */
    } else {
        /*@ assert i <= len; */
        /*@ assert \exists integer k;
              0 <= k && k < i && IsEvenP(k) && !IsEvenP(lst[k]); */
        /*@ assert \exists integer k;
              0 <= k && k < len && IsEvenP(k) && !IsEvenP(lst[k]); */
        /*@ assert !(\forall integer k;
              0 <= k && k < len ==> (IsEvenP(k) ==> IsEvenP(lst[k]))); */
    }

    return result;
}