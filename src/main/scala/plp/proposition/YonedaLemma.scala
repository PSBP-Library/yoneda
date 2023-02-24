package plp.proposition

import plp.notation.{Law, =:}

import plp.specification.{Category, Functor, NaturalTransformation}

import plp.implementation.specific.{Fun, functionCategory}

import plp.implementation.generic.{Yoneda, yonedaFunctor}

class YonedaLemma[
    Arr[-_, +_]: Category,
    Z,
    G[+_]: [_[+_]] =>> Functor[Arr, Fun, G]
]:

  val c = summon[Category[Arr]]

  import c.{`__-->__`}

  def g[Z, Y]: Arr[Z, Y] => Fun[G[Z], G[Y]] =
    summon[Functor[Arr, Fun, G]].lift[Z, Y]

  type YF = [Z] =>> [__] =>> Yoneda[Arr][Z][__]

  def yonedaLemma1[Y]: (
      NaturalTransformation[Arr, Fun, YF[Z], G] => Law[Fun[YF[Z][Y], G[Y]]]
  ) =
    yfz2g =>

      def `z-->z`[Z] = `__-->__`[Z]

      def tau[__]: Fun[YF[Z][__], G[__]] = yfz2g.transform

      val `g[z]` : G[Z] = tau(`z-->z`)

      val yfz_2_g: NaturalTransformation[Arr, Fun, YF[Z], G] =
        new:
          def transform[__]: Fun[YF[Z][__], G[__]] =
            `z-->__` => g(`z-->__`)(`g[z]`)

      def sigma[__]: Fun[YF[Z][__], G[__]] = yfz_2_g.transform

      tau =:
        sigma

  def yonedaLemma2[Y, X]: G[Z] => (Arr[Y, X] => (Law[Fun[YF[Z][Y], G[X]]])) =
    `g[z]` =>

      val yfz2g: NaturalTransformation[Arr, Fun, YF[Z], G] =
        new:
          def transform[__]: Fun[YF[Z][__], G[__]] =
            `z-->__` => g(`z-->__`)(`g[z]`)

      def tau[__]: Fun[YF[Z][__], G[__]] = yfz2g.transform

      val yf: Arr[Y, X] => Fun[YF[Z][Y], YF[Z][X]] = yonedaFunctor.lift

      `y-->x` =>
        (g(`y-->x`) o tau) =:
          (tau o yf(`y-->x`))

import plp.notation.{Proof, ==:, qed}

class YonedaLemmaProof[
    Z,
    Arr[-_, +_]: Category,
    G[+_]: [_[+_]] =>> Functor[Arr, Fun, G]
]:

  val c = summon[Category[Arr]]

  def g[Z, Y]: Arr[Z, Y] => Fun[G[Z], G[Y]] =
    summon[Functor[Arr, Fun, G]].lift[Z, Y]

  type YF = [Z] =>> [__] =>> Yoneda[Arr][Z][__]

  def yf[Y, X]: Arr[Y, X] => Fun[YF[Z][Y], YF[Z][X]] = yonedaFunctor.lift

  def yonedaLemma1Proof[Y]
      : NaturalTransformation[Arr, Fun, YF[Z], G] => (YF[Z][Y] => Proof[G[Y]]) =
    yfz2g =>

      import c.`__-->__`

      def `z-->z`[Z] = `__-->__`[Z]

      def tau[__]: Fun[YF[Z][__], G[__]] = yfz2g.transform

      val `g[z]` : G[Z] =
        tau(`z-->z`)

      val yfz_2_g: NaturalTransformation[Arr, Fun, YF[Z], G] =
        new:
          def transform[__]: Fun[YF[Z][__], G[__]] =
            `z-->__` => g(`z-->__`)(`g[z]`)

      def sigma[__]: Fun[YF[Z][__], G[__]] = yfz_2_g.transform

      `z-->y` =>
        tau(`z-->y`) ==:
          // rightIdentityLaw for Arr
          tau(`z-->y` o `z-->z`) ==:
          // definition yf
          tau(yf(`z-->y`)(`z-->z`)) ==:
          // definition o for functionCategory
          (tau o yf(`z-->y`))(`z-->z`) ==:
          // naturalTransformationLaw for tau
          (g(`z-->y`) o tau)(`z-->z`) ==:
          // definition o for functionCategory
          g(`z-->y`)(tau(`z-->z`)) ==:
          // definition `g[z]`
          g(`z-->y`)(`g[z]`) ==:
          // definition sigma
          sigma(`z-->y`) ==:
          // done
          qed

  def yonedaLemma2Proof[Y, X]
      : G[Z] => (Arr[Y, X] => (YF[Z][Y] => Proof[G[X]])) =
    `g[z]` =>
      `y-->x` =>

        val yfz2g: NaturalTransformation[Arr, Fun, YF[Z], G] =
          new:
            def transform[__]: Fun[YF[Z][__], G[__]] =
              `z-->__` => g(`z-->__`)(`g[z]`)

        def tau[__]: Fun[YF[Z][__], G[__]] = yfz2g.transform

        `z-->y` =>
          (g(`y-->x`) o tau)(`z-->y`) ==:
            // definition o for functionCategory
            g(`y-->x`)(tau(`z-->y`)) ==:
            // definition tau
            g(`y-->x`)(g(`z-->y`)(`g[z]`)) ==:
            // definition o for functionCategory
            (g(`y-->x`) o g(`z-->y`))(`g[z]`) ==:
            // compositionLaw for g
            (g(`y-->x` o `z-->y`))(`g[z]`) ==:
            // definition yf
            (g(yf(`y-->x`)(`z-->y`)))(`g[z]`) ==:
            // definition tau
            tau(yf(`y-->x`)(`z-->y`)) ==:
            // definition o for functionCategory
            (tau o yf(`y-->x`))(`z-->y`) ==:
            // done
            qed
