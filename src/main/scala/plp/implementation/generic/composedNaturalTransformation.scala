package plp.implementation.generic

import plp.specification.{Category, Functor, NaturalTransformation}

def composedNaturalTransformation[
    Arr[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr, Arr, F],
    G[+_]: [_[+_]] =>> Functor[Arr, Arr, G],
    H[+_]: [_[+_]] =>> Functor[Arr, Arr, H],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr, Arr, F, G],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr, Arr, G, H]
]: NaturalTransformation[Arr, Arr, F, H] =

  def alpha[__] = summon[NaturalTransformation[Arr, Arr, F, G]].transform[__]

  def beta[__] = summon[NaturalTransformation[Arr, Arr, G, H]].transform[__]

  new {
    override def transform[__]: Arr[F[__], H[__]] =
      beta o alpha
  }

import plp.notation.{Proof, ==:, qed}

class ComposedNaturalTransformationProof[
    Arr[-_, +_]: Category,
    F[+_]: [_[+_]] =>> Functor[Arr, Arr, F],
    G[+_]: [_[+_]] =>> Functor[Arr, Arr, G],
    H[+_]: [_[+_]] =>> Functor[Arr, Arr, H],
    S[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr, Arr, F, G],
    T[_[-_, +_], _[-_, +_], _[+_], _[+_]]: [_[
        _[-_, +_],
        _[-_, +_],
        _[+_],
        _[+_]
    ]] =>> NaturalTransformation[Arr, Arr, G, H]
]:

  def naturalTransformationProof[Z, Y]: Arr[Z, Y] => Proof[Arr[F[Z], H[Y]]] =

    def alpha[__] = summon[NaturalTransformation[Arr, Arr, F, G]].transform[__]

    def beta[__] = summon[NaturalTransformation[Arr, Arr, G, H]].transform[__]

    def tau[__] =
      composedNaturalTransformation[Arr, F, G, H, S, T].transform[__]

    def f[Z, Y]: Arr[Z, Y] => Arr[F[Z], F[Y]] =
      summon[Functor[Arr, Arr, F]].lift

    def g[Z, Y]: Arr[Z, Y] => Arr[G[Z], G[Y]] =
      summon[Functor[Arr, Arr, G]].lift
      
    def h[Z, Y]: Arr[Z, Y] => Arr[H[Z], H[Y]] =
      summon[Functor[Arr, Arr, H]].lift

    `z-->y` =>
      (tau o f(`z-->y`)) ==:
        // definition tau
        ((beta o alpha) o f(`z-->y`)) ==:
        // categoryCompositionAssociativityLaw for Arr
        (beta o (alpha o f(`z-->y`))) ==:
        // naturalTransformationLaw for S
        (beta o (g(`z-->y`) o alpha)) ==:
        // categoryCompositionAssociativityLaw for Arr
        ((beta o g(`z-->y`)) o alpha) ==:
        // naturalTransformationLaw for T
        ((h(`z-->y`) o beta) o alpha) ==:
        // categoryCompositionAssociativityLaw for Arr
        (h(`z-->y`) o (beta o alpha)) ==:
        // definition tau
        (h(`z-->y`) o tau) ==:
        // done
        qed

