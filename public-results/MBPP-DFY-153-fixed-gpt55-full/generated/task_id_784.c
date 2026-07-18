/*@
  predicate IsEven(integer n) =
    n % 2 == 0;

  predicate IsOdd(integer n) =
    n % 2 != 0;

  predicate IsFirstEven{L}(integer evenIndex, int *lst, integer len) =
    0 <= evenIndex &&
    evenIndex < len &&
    IsEven(\at(lst[evenIndex], L)) &&
    (\forall integer i; 0 <= i && i < evenIndex ==> IsOdd(\at(lst[i], L)));

  predicate IsFirstOdd{L}(integer oddIndex, int *lst, integer len) =
    0 <= oddIndex &&
    oddIndex < len &&
    IsOdd(\at(lst[oddIndex], L)) &&
    (\forall integer i; 0 <= i && i < oddIndex ==> IsEven(\at(lst[i], L)));
*/

/*@
  requires len >= 2;
  requires \valid_read(lst + (0 .. len-1));
  requires \valid(evenIndex);
  requires \valid(oddIndex);
  requires \separated(evenIndex, oddIndex, lst + (0 .. len-1));
  requires \exists integer i; 0 <= i && i < len && IsEven(lst[i]);
  requires \exists integer i; 0 <= i && i < len && IsOdd(lst[i]);

  assigns *evenIndex, *oddIndex;

  ensures 0 <= *evenIndex && *evenIndex < len;
  ensures 0 <= *oddIndex && *oddIndex < len;
  ensures IsEven(lst[*evenIndex]);
  ensures IsFirstEven(*evenIndex, lst, len);
  ensures IsOdd(lst[*oddIndex]);
  ensures IsFirstOdd(*oddIndex, lst, len);
*/
void FirstEvenOddIndices(int *lst, int len, int *evenIndex, int *oddIndex)
{
    int i = 0;

    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant \forall integer j; 0 <= j && j < i ==> IsOdd(lst[j]);
      loop assigns i;
      loop variant len - i;
    */
    while (i < len && lst[i] % 2 != 0) {
        i++;
    }

    //@ assert i < len;
    //@ assert IsEven(lst[i]);
    *evenIndex = i;

    i = 0;

    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant \forall integer j; 0 <= j && j < i ==> IsEven(lst[j]);
      loop assigns i;
      loop variant len - i;
    */
    while (i < len && lst[i] % 2 == 0) {
        i++;
    }

    //@ assert i < len;
    //@ assert IsOdd(lst[i]);
    *oddIndex = i;
}

/*@
  requires len >= 2;
  requires \valid_read(lst + (0 .. len-1));
  requires \exists integer i; 0 <= i && i < len && IsEven(lst[i]);
  requires \exists integer i; 0 <= i && i < len && IsOdd(lst[i]);

  assigns \nothing;

  ensures \exists integer i, j;
            0 <= i && i < len &&
            IsEven(lst[i]) &&
            IsFirstEven(i, lst, len) &&
            0 <= j && j < len &&
            IsOdd(lst[j]) &&
            IsFirstOdd(j, lst, len) &&
            \result == lst[i] * lst[j];
*/
long long ProductEvenOdd(int *lst, int len)
{
    int evenIndex = 0;
    int oddIndex = 0;

    FirstEvenOddIndices(lst, len, &evenIndex, &oddIndex);

    return (long long)lst[evenIndex] * (long long)lst[oddIndex];
}