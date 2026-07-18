/*@
  requires radius > 0.0;
  requires \is_finite(radius);
  requires \is_finite(
    (double)(
      (double)(
        (double)(
          (double)(
            (double)4.0 / (double)3.0
          ) * (double)3.1415926535
        ) * radius
      ) * radius
    ) * radius
  );
  assigns \nothing;
  ensures \result ==
    (double)(
      (double)(
        (double)(
          (double)(
            (double)4.0 / (double)3.0
          ) * (double)3.1415926535
        ) * radius
      ) * radius
    ) * radius;
  ensures \is_finite(\result);
*/
double SphereVolume(double radius)
{
    return (double)(
        (double)(
            (double)(
                (double)(
                    (double)4.0 / (double)3.0
                ) * (double)3.1415926535
            ) * radius
        ) * radius
    ) * radius;
}