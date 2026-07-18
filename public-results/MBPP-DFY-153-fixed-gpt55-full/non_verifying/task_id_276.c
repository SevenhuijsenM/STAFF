#include <float.h>

static const double PI = 3.14159265359;

/*@
  requires \rounding_mode(\NearestEven);
  requires \is_finite(PI);
  requires \is_finite(radius);
  requires \is_finite(height);
  requires 0.0 < radius;
  requires 0.0 < height;
  requires \is_finite(\round_double(\NearestEven, PI * radius));
  requires \is_finite(\round_double(\NearestEven,
                    \round_double(\NearestEven, PI * radius) * radius));
  requires \is_finite(\round_double(\NearestEven,
                    \round_double(\NearestEven,
                      \round_double(\NearestEven, PI * radius) * radius) * height));
  assigns \nothing;
  ensures \result == \round_double(\NearestEven,
                    \round_double(\NearestEven,
                      \round_double(\NearestEven, PI * radius) * radius) * height);
  ensures \is_finite(\result);
*/
double CylinderVolume(double radius, double height)
{
    double t1 = PI * radius;
    //@ assert t1 == \round_double(\NearestEven, PI * radius);
    //@ assert \is_finite(t1);

    double t2 = t1 * radius;
    //@ assert t2 == \round_double(\NearestEven, t1 * radius);
    //@ assert t2 == \round_double(\NearestEven, \round_double(\NearestEven, PI * radius) * radius);
    //@ assert \is_finite(t2);

    double volume = t2 * height;
    //@ assert volume == \round_double(\NearestEven, t2 * height);
    //@ assert volume == \round_double(\NearestEven, \round_double(\NearestEven, \round_double(\NearestEven, PI * radius) * radius) * height);
    //@ assert \is_finite(volume);

    return volume;
}