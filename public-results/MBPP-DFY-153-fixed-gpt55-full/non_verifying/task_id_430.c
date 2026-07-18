/*@
  requires \is_finite(a);
  requires \is_finite(h);
  requires \is_finite(k);
  requires a != 0.0;
  requires \is_finite(4.0 * a);
  requires 4.0 * a != 0.0;
  requires \is_finite(1.0 / (4.0 * a));
  requires \is_finite(k - 1.0 / (4.0 * a));
  assigns \nothing;
  ensures \is_finite(\result);
  ensures \result == k - 1.0 / (4.0 * a);
*/
double ParabolaDirectrix(double a, double h, double k)
{
    (void) h;
    return k - 1.0 / (4.0 * a);
}