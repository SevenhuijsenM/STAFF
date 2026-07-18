/*@
  requires \is_finite(radius);
  requires \is_finite(height);
  requires radius > 0.0;
  requires height > 0.0;
  requires \is_finite(radius * height);
  requires \is_finite(2.0 * (radius * height));
  requires \is_finite((2.0 * (radius * height)) * 3.14);
  assigns \nothing;
  ensures \is_finite(\result);
  ensures \result == (2.0 * (radius * height)) * 3.14;
*/
double CylinderLateralSurfaceArea(double radius, double height) {
  double area = (2.0 * (radius * height)) * 3.14;
  //@ assert area == (2.0 * (radius * height)) * 3.14;
  //@ assert \is_finite(area);
  return area;
}