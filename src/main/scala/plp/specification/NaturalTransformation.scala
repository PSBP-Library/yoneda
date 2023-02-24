package plp.specification

trait NaturalTransformation[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    G[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, G]
]:

  def transform[__]: Arr_D[F[__], G[__]]

import plp.notation.{Law, =:}

class NaturalTransformationLaw[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    G[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, G],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr_C, Arr_D, F, G]
]:

  def naturalTransformationLaw[Z, Y]: Arr_C[Z, Y] => Law[Arr_D[F[Z], G[Y]]] =
    `z-->y` =>

      def tau[__]: Arr_D[F[__], G[__]] =
        summon[NaturalTransformation[Arr_C, Arr_D, F, G]].transform

      val f: Arr_C[Z, Y] => Arr_D[F[Z], F[Y]] =
        summon[Functor[Arr_C, Arr_D, F]].lift

      val g: Arr_C[Z, Y] => Arr_D[G[Z], G[Y]] =
        summon[Functor[Arr_C, Arr_D, G]].lift

      extension [Z, Y, X](`y-->x`: Arr_D[Y, X])
        def o_d(`z-->y`: Arr_D[Z, Y]): Arr_D[Z, X] =
          summon[Category[Arr_D]].o(`y-->x`)(`z-->y`)

      (tau o_d f(`z-->y`)) =:
        (g(`z-->y`) o_d tau)
