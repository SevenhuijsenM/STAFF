#include <stdbool.h>

/*@
  requires 100 <= n && n < 1000;
  assigns \nothing;
  ensures (\result != 0) <==> 
    (n == ((n / 100) * (n / 100) * (n / 100)
         + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10)
         + (n % 10) * (n % 10) * (n % 10)));
*/
bool IsArmstrong(int n) {
    int a = n / 100;
    int b = (n / 10) % 10;
    int c = n % 10;

    bool result = (n == (a * a * a + b * b * b + c * c * c));
    return result;
}