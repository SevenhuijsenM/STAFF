#include <stdbool.h>
#include <stddef.h>

/*@
  requires n == 0 || \valid_read(s + (0 .. n - 1));
  assigns \nothing;
  ensures (\result != 0) <==> (\exists integer i; 0 <= i && i < n && (s[i] == 'z' || s[i] == 'Z'));
*/
bool ContainsZ(const char *s, size_t n)
{
    bool result = false;
    size_t i;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant result == 0;
      loop invariant \forall integer k; 0 <= k && k < i ==> !(s[k] == 'z' || s[k] == 'Z');
      loop invariant (result != 0) <==> (\exists integer k; 0 <= k && k < i && (s[k] == 'z' || s[k] == 'Z'));
      loop assigns i, result;
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        if (s[i] == 'z' || s[i] == 'Z') {
            result = true;
            //@ assert 0 <= i && i < n;
            //@ assert \exists integer k; 0 <= k && k < n && (s[k] == 'z' || s[k] == 'Z');
            return result;
        }
    }

    //@ assert i == n;
    //@ assert \forall integer k; 0 <= k && k < n ==> !(s[k] == 'z' || s[k] == 'Z');
    //@ assert !(\exists integer k; 0 <= k && k < n && (s[k] == 'z' || s[k] == 'Z'));
    //@ assert (result != 0) <==> (\exists integer k; 0 <= k && k < n && (s[k] == 'z' || s[k] == 'Z'));

    return result;
}