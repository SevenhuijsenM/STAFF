#define C_TWO_PI 0x1.921fb54442d18p+2
#define C_MAX_SAFE_RADIUS 0x1.0p+1000

/*@
  requires \is_finite(radius);
  requires 0.0 < radius;
  requires radius <= C_MAX_SAFE_RADIUS;
  requires \is_finite(C_TWO_PI * radius);
  assigns \nothing;
  ensures \is_finite(\result);
  ensures \result == C_TWO_PI * radius;
*/
double CircleCircumference(double radius)
{
    double circumference = C_TWO_PI * radius;
    return circumference;
}