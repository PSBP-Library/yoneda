package plp.implementation.generic

import plp.notation.{O}

import plp.specification.{Category, Functor, NaturalTransformation}

def leftFunctorComposedNaturalTransformation[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    Arr_E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    H[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, H],
    K[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, K],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr_D, Arr_E, H, K]
]: NaturalTransformation[Arr_C, Arr_E, H O F, K O F] =

  given `hof`: Functor[Arr_C, Arr_E, H O F] =
    composedFunctor[Arr_C, Arr_D, Arr_E, F, H]

  given `kof`: Functor[Arr_C, Arr_E, K O F] =
    composedFunctor[Arr_C, Arr_D, Arr_E, F, K]

  def beta[__] = summon[NaturalTransformation[Arr_D, Arr_E, H, K]].transform[__]

  new {
    override def transform[__]: Arr_E[(H O F)[__], (K O F)[__]] =
      beta[F[__]]
  }

import plp.notation.{Proof, ==:, qed}

import plp.implementation.specific.{functionCategory}

class LeftFunctorComposedNaturalTransformationProof[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    Arr_E[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    H[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, H],
    K[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, K],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr_D, Arr_E, H, K]
]:

  def naturalTransformationProof[Z, Y]
      : Arr_C[Z, Y] => Proof[Arr_E[(H O F)[Z], (K O F)[Y]]] =
    `z-->y` =>

      def beta[__] =
        summon[NaturalTransformation[Arr_D, Arr_E, H, K]].transform[__]

      def tau[__] =
        leftFunctorComposedNaturalTransformation[
          Arr_C,
          Arr_D,
          Arr_E,
          F,
          H,
          K,
          S
        ]
          .transform[__]

      def f[Z, Y]: Arr_C[Z, Y] => Arr_D[F[Z], F[Y]] =
        summon[Functor[Arr_C, Arr_D, F]].lift

      def h[Z, Y]: Arr_D[Z, Y] => Arr_E[H[Z], H[Y]] =
        summon[Functor[Arr_D, Arr_E, H]].lift

      def k[Z, Y]: Arr_D[Z, Y] => Arr_E[K[Z], K[Y]] =
        summon[Functor[Arr_D, Arr_E, K]].lift

      (tau o (h o f)(`z-->y`)) ==:
        // definition tau
        (beta[F[Y]] o (h o f)(`z-->y`)) ==:
        // definition o for functionCategory
        (beta[F[Y]] o h(f(`z-->y`))) ==:
        // naturalTransformationLaw for S (with f(`z-->y`))
        (k(f(`z-->y`)) o beta[F[Z]]) ==:
        // definition o for functionCategory
        ((k o f)(`z-->y`) o beta[F[Z]]) ==:
        // definition tau
        ((k o f)(`z-->y`) o tau) ==:
        // done
        qed
