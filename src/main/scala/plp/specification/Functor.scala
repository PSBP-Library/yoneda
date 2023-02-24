package plp.specification

trait Functor[Arr_C[-_, +_]: Category, Arr_D[-_, +_]: Category, F[+_]]
    extends GraphMorphism[Arr_C, Arr_D, F]

import plp.notation.{Law, =:}

class FunctorLaws[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F]
]:

  def f[Z, Y]: Arr_C[Z, Y] => Arr_D[F[Z], F[Y]] =
    summon[Functor[Arr_C, Arr_D, F]].lift

  def functorCompositionLaw[Z, Y, X]
      : (Arr_C[Z, Y], Arr_C[Y, X]) => Law[Arr_D[F[Z], F[X]]] =
    (`z-->y`, `y-->x`) =>

      extension [Z, Y, X](`y-->x`: Arr_C[Y, X])
        def o_c(`z-->y`: Arr_C[Z, Y]): Arr_C[Z, X] =
          summon[Category[Arr_C]].o[Z, Y, X](`y-->x`)(`z-->y`)

      extension [Z, Y, X](`y-->x`: Arr_D[Y, X])
        def o_d(`z-->y`: Arr_D[Z, Y]): Arr_D[Z, X] =
          summon[Category[Arr_D]].o[Z, Y, X](`y-->x`)(`z-->y`)

      (f(`y-->x` o_c `z-->y`)) =:
        (f(`y-->x`) o_d f(`z-->y`))

  def functorIdentityLaw[Z]: Law[Arr_D[F[Z], F[Z]]] =

    val `z-c->z` = summon[Category[Arr_C]].`__-->__`[Z]

    val `f[z]-d->f[z]` = summon[Category[Arr_D]].`__-->__`[F[Z]]

    (f(`z-c->z`)) =:
      (`f[z]-d->f[z]`)

type EndoFunctor[Arr[-_, +_], F[+_]] = Functor[Arr, Arr, F]
