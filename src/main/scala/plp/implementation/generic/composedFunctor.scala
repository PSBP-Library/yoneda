package plp.implementation.generic

import plp.notation.{O}

import plp.specification.{Category, Functor}

import plp.implementation.specific.{functionCategory}

given composedFunctor[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    Arr_E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    G[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, G]
]: Functor[Arr_C, Arr_E, G O F] with

  def lift[Z, Y]: Arr_C[Z, Y] => Arr_E[(G O F)[Z], (G O F)[Y]] =

    val f: Arr_C[Z, Y] => Arr_D[F[Z], F[Y]] =
      summon[Functor[Arr_C, Arr_D, F]].lift

    val g: Arr_D[F[Z], F[Y]] => Arr_E[G[F[Z]], G[F[Y]]] =
      summon[Functor[Arr_D, Arr_E, G]].lift

    `z-->y` => g(f(`z-->y`))

import plp.notation.{Proof, ==:, qed}

class ComposedFunctorProofs[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    Arr_E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    G[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, G]
]:

  def f[Z, Y]: Arr_C[Z, Y] => Arr_D[F[Z], F[Y]] =
    summon[Functor[Arr_C, Arr_D, F]].lift

  def g[Z, Y]: Arr_D[F[Z], F[Y]] => Arr_E[G[F[Z]], G[F[Y]]] =
    summon[Functor[Arr_D, Arr_E, G]].lift

  def `gof`[Z, Y]: Arr_C[Z, Y] => Arr_E[G[F[Z]], G[F[Y]]] =
    composedFunctor[Arr_C, Arr_D, Arr_E, F, G].lift

  def functorCompositionProof[Z, Y, X]
      : Arr_C[Z, Y] => (Arr_C[Y, X] => Proof[Arr_E[(G O F)[Z], (G O F)[X]]]) =
    `z-->y` =>
      `y-->x` =>

        extension [Z, Y, X](`y-->x`: Arr_C[Y, X])
          def o_c(`z-->y`: Arr_C[Z, Y]): Arr_C[Z, X] =
            summon[Category[Arr_C]].o[Z, Y, X](`y-->x`)(`z-->y`)

        extension [Z, Y, X](`y-->x`: Arr_D[Y, X])
          def o_d(`z-->y`: Arr_D[Z, Y]): Arr_D[Z, X] =
            summon[Category[Arr_D]].o[Z, Y, X](`y-->x`)(`z-->y`)

        extension [Z, Y, X](`y-->x`: Arr_E[Y, X])
          def o_e(`z-->y`: Arr_E[Z, Y]): Arr_E[Z, X] =
            summon[Category[Arr_E]].o[Z, Y, X](`y-->x`)(`z-->y`)

        (`gof`(`y-->x` o_c `z-->y`)) ==:
          // definition lift for composedFunctor
          (g(f(`y-->x` o_c `z-->y`))) ==:
          // functorCompositionLaw for f
          (g(f(`y-->x`) o_d f(`z-->y`))) ==:
          // functorCompositionLaw for g
          (g(f(`y-->x`)) o_e g(f(`z-->y`))) ==:
          // definition lift for composedFunctor
          (`gof`(`y-->x`) o_e `gof`(`z-->y`)) ==:
          // done
          qed

  def functorIdentityProof[Z]: Proof[Arr_E[(G O F)[Z], (G O F)[Z]]] =

    val `z-c->z` = summon[Category[Arr_C]].`__-->__`[Z]

    val `f[z]-d->f[z]` = summon[Category[Arr_D]].`__-->__`[F[Z]]

    val `(gof)[z]-e->(gof)[z]` = summon[Category[Arr_E]].`__-->__`[(G O F)[Z]]

    (`gof`(`z-c->z`)) ==:
      // definition lift for composedFunctor
      (g(f(`z-c->z`))) ==:
      // functorIdentityLaw for f
      (g(`f[z]-d->f[z]`)) ==:
      // functorIdentityLaw for g
      (`(gof)[z]-e->(gof)[z]`) ==:
      // done
      qed
