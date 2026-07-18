#define DAFNY_PI ((double)3.14159265358979323846)

/*@
  requires \is_finite(degrees);
  requires -1.0e300 <= degrees;
  requires degrees <= 1.0e300;
  assigns \nothing;
  ensures \exact(\result) ==
          \round_double(\NearestEven,
            \round_double(\NearestEven, \exact(degrees) * \exact(DAFNY_PI)) / 180.0);
  ensures \is_finite(\result);
*/
double DegreesToRadians(double degrees) {
    //@ assert \is_finite(DAFNY_PI);
    double product = degrees * DAFNY_PI;
    //@ assert \is_finite(product);
    //@ assert \exact(product) == \round_double(\NearestEven, \exact(degrees) * \exact(DAFNY_PI));
    double radians = product / 180.0;
    //@ assert \is_finite(radians);
    //@ assert \exact(radians) == \round_double(\NearestEven, \exact(product) / 180.0);
    //@ assert \exact(radians) == \round_double(\NearestEven, \round_double(\NearestEven, \exact(degrees) * \exact(DAFNY_PI)) / 180.0);
    return radians;
}