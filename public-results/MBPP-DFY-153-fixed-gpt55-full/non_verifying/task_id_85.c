#define SPHERE_PI 0x1.921fb54442d18p+1
#define SPHERE_FOUR_PI 0x1.921fb54442d18p+3

/*@
  requires \is_finite(radius);
  requires radius > 0.0;
  requires \is_finite(SPHERE_FOUR_PI);
  requires \is_finite(SPHERE_FOUR_PI * radius);
  requires \is_finite((SPHERE_FOUR_PI * radius) * radius);
  assigns \nothing;
  ensures \is_finite(\result);
  ensures \result == ((SPHERE_FOUR_PI * radius) * radius);
*/
double SphereSurfaceArea(double radius)
{
    return (SPHERE_FOUR_PI * radius) * radius;
}