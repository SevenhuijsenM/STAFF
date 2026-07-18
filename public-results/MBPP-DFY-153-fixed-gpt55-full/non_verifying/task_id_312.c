#define PI 3.14159265358979323846
#define ONE_THIRD (1.0 / 3.0)
#define CONE_COEFF (ONE_THIRD * PI)

/*@
  requires radius > 0.0;
  requires height > 0.0;
  requires \is_finite(radius);
  requires \is_finite(height);
  requires \is_finite(CONE_COEFF);
  requires \is_finite(CONE_COEFF * radius);
  requires \is_finite((CONE_COEFF * radius) * radius);
  requires \is_finite(((CONE_COEFF * radius) * radius) * height);
  assigns \nothing;
  ensures \is_finite(\result);
  ensures \result == CONE_COEFF * radius * radius * height;
*/
double ConeVolume(double radius, double height)
{
    //@ assert radius > 0.0;
    //@ assert height > 0.0;
    //@ assert \is_finite(radius);
    //@ assert \is_finite(height);
    //@ assert \is_finite(CONE_COEFF);
    //@ assert \is_finite(CONE_COEFF * radius);
    //@ assert \is_finite((CONE_COEFF * radius) * radius);
    //@ assert \is_finite(((CONE_COEFF * radius) * radius) * height);

    double volume = CONE_COEFF * radius * radius * height;

    //@ assert \is_finite(volume);
    //@ assert volume == CONE_COEFF * radius * radius * height;

    return volume;
}