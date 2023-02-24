package plp.implementation.generic

import plp.notation.{O}

import plp.specification.{Category, Functor, NaturalTransformation}

def rightFunctorComposedNaturalTransformation[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    Arr_E[-_, +_]: Category,
    H[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, H],
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    G[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, G],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr_C, Arr_D, F, G]
]: NaturalTransformation[Arr_C, Arr_E, H O F, H O G] =

  given `hof`: Functor[Arr_C, Arr_E, H O F] =
    composedFunctor[Arr_C, Arr_D, Arr_E, F, H]

  given `hog`: Functor[Arr_C, Arr_E, H O G] =
    composedFunctor[Arr_C, Arr_D, Arr_E, G, H]

  def alpha[__]: Arr_D[F[__], G[__]] =
    summon[NaturalTransformation[Arr_C, Arr_D, F, G]].transform[__]

  def h[Z, Y]: Arr_D[Z, Y] => Arr_E[H[Z], H[Y]] =
    summon[Functor[Arr_D, Arr_E, H]].lift

  new {
    override def transform[__]: Arr_E[(H O F)[__], (H O G)[__]] =
      h(alpha[__])
  }

import plp.notation.{Proof, ==:, qed}

import plp.implementation.specific.{functionCategory}

class RightFunctorComposedNaturalTransformationProof[
    Arr_C[-_, +_]: Category,
    Arr_D[-_, +_]: Category,
    Arr_E[-_, +_]: Category,
    H[+_]: [_[+_]] =>> Functor[Arr_D, Arr_E, H],
    F[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, F],
    G[+_]: [_[+_]] =>> Functor[Arr_C, Arr_D, G],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr_C, Arr_D, F, G]
]:

  def naturalTransformationProof[Z, Y]
      : Arr_C[Z, Y] => Proof[Arr_E[(H O F)[Z], (H O G)[Y]]] =
    `z-->y` =>

      def alpha[__]: Arr_D[F[__], G[__]] =
        summon[NaturalTransformation[Arr_C, Arr_D, F, G]].transform[__]

      def tau[__] =
        rightFunctorComposedNaturalTransformation[
          Arr_C,
          Arr_D,
          Arr_E,
          H,
          F,
          G,
          T
        ]
          .transform[__]

      def h[Z, Y]: Arr_D[Z, Y] => Arr_E[H[Z], H[Y]] =
        summon[Functor[Arr_D, Arr_E, H]].lift

      def f[Z, Y]: Arr_C[Z, Y] => Arr_D[F[Z], F[Y]] =
        summon[Functor[Arr_C, Arr_D, F]].lift

      def g[Z, Y]: Arr_C[Z, Y] => Arr_D[G[Z], G[Y]] =
        summon[Functor[Arr_C, Arr_D, G]].lift

      (tau o (h o f)(`z-->y`)) ==:
        // definition tau
        (h(alpha) o (h o f)(`z-->y`)) ==:
        // definition o for functionCategory
        (h(alpha) o h(f(`z-->y`))) ==:
        // functorCompositionLaw for h
        (h(alpha o f(`z-->y`))) ==:
        // naturalTransformationLaw for T
        (h(g(`z-->y`) o alpha)) ==:
        // functorCompositionLaw for h
        (h(g(`z-->y`)) o h(alpha)) ==:
        // definition o for functionCategory
        ((h o g)(`z-->y`) o h(alpha)) ==:
        // definition tau
        ((h o g)(`z-->y`) o tau) ==:
        // done
        qed
