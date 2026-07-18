/*@
  requires \is_finite(radius);
  requires \is_finite(height);
  requires 0.0 < radius;
  requires 0.0 < height;
  requires \is_finite(\round_double(\NearestEven, radius + height));
  requires \is_finite(\round_double(\NearestEven, 0x1.921fb54442d18p+2 * radius));
  requires \is_finite(\round_double(\NearestEven,
                    \round_double(\NearestEven, 0x1.921fb54442d18p+2 * radius) *
                    \round_double(\NearestEven, radius + height)));
  assigns \nothing;
  ensures \is_finite(\result);
  ensures \result == \round_double(\NearestEven,
                    \round_double(\NearestEven, 0x1.921fb54442d18p+2 * radius) *
                    \round_double(\NearestEven, radius + height));
*/
double CylinderSurfaceArea(double radius, double height)
{
    double radius_plus_height = radius + height;
    //@ assert radius_plus_height == \round_double(\NearestEven, radius + height);
    //@ assert \is_finite(radius_plus_height);

    double scaled_radius = 0x1.921fb54442d18p+2 * radius;
    //@ assert scaled_radius == \round_double(\NearestEven, 0x1.921fb54442d18p+2 * radius);
    //@ assert \is_finite(scaled_radius);

    double area = scaled_radius * radius_plus_height;
    //@ assert area == \round_double(\NearestEven, scaled_radius * radius_plus_height);
    //@ assert scaled_radius * radius_plus_height == \round_double(\NearestEven, 0x1.921fb54442d18p+2 * radius) * \round_double(\NearestEven, radius + height);
    //@ assert area == \round_double(\NearestEven, \round_double(\NearestEven, 0x1.921fb54442d18p+2 * radius) * \round_double(\NearestEven, radius + height));
    //@ assert \is_finite(area);

    return area;
}