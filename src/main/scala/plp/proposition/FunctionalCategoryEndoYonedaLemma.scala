package plp.proposition

import plp.notation.{O, U, Law, =:}

import plp.specification.{
  FunctionalCategory,
  EndoFunctor,
  NaturalTransformation
}

import plp.implementation.generic.{composedFunctor, yonedaEndoFunctor}

import plp.implementation.specific.{functionCategory}

class FunctionalCategoryEndoYonedaLemma[
    Z,
    Arr[-_, +_]: FunctionalCategory,
    G[+_]: [G[+_]] =>> EndoFunctor[Arr, G]
]:

  val fc = summon[FunctionalCategory[Arr]]

  import fc.{YEF}

  def g[Z, Y]: Arr[Z, Y] => Arr[G[Z], G[Y]] = summon[EndoFunctor[Arr, G]].lift

  def endoYonedaLemma1[Y]
      : NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] => Law[
        Arr[YEF[Z][Y], (YEF[U] O G)[Y]]
      ] =
    yz2yu_o_g =>

      import fc.{`__-->__`, v2gv, yef, mu}

      val `z-->z` = `__-->__`[Z]

      def tau[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yz2yu_o_g.transform

      val `u-->(u-->g[z])` : (YEF[U] O YEF[U] O G)[Z] =
        tau o v2gv(`z-->z`)

      val yz_2_yu_o_g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
        new:
          def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
            mu o fc.f2a(`z-->__` => (yef o g)(`z-->__`) o `u-->(u-->g[z])`)

      def sigma[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yz_2_yu_o_g.transform

      tau =:
        sigma

  def endoYonedaLemma2[Y, X]: (YEF[U] O YEF[U] O G)[Z] => (
      Arr[Y, X] => Law[Arr[YEF[Z][Y], (YEF[U] O G)[X]]]
  ) =
    `u-->(u-->g[z])` =>
      `y-->x` =>

        import fc.{yef, mu}

        val yz2yu_o_g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
          new:
            def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
              mu o fc.f2a(`z-->__` => (yef o g)(`z-->__`) o `u-->(u-->g[z])`)

        def tau[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yz2yu_o_g.transform

        ((yef o g)(`y-->x`) o tau) =:
          (tau o yef(`y-->x`))

  def endoYonedaLemma1Corollary[Y]
      : NaturalTransformation[Arr, Arr, YEF[Z], G] => Law[
        Arr[YEF[Z][Y], (YEF[U] O G)[Y]]
      ] =
    yef2g =>

      import fc.{eta}

      def tau[__]: Arr[YEF[Z][__], G[__]] = yef2g.transform

      endoYonedaLemma1[Y](
        new {
          override def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
            eta o tau
        }
      )

import plp.notation.{Proof, ==:, qed}

class FunctionalCategoryEndoYonedaProof[
    Z,
    Arr[-_, +_]: FunctionalCategory,
    G[+_]: [G[+_]] =>> EndoFunctor[Arr, G]
]:

  val fc = summon[FunctionalCategory[Arr]]

  import fc.{YEF}

  def g[Z, Y]: Arr[Z, Y] => Arr[G[Z], G[Y]] = summon[EndoFunctor[Arr, G]].lift

  def endoYonedaProof1[Y]
      : NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] => (
          Arr[Z, Y] => Proof[(YEF[U] O YEF[U] O G)[Y]]
      ) =
    yz2yu_o_g =>

      import fc.{`__-->__`, v2gv, yef, eta, mu}

      val `z-->z` = `__-->__`[Z]

      def tau[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yz2yu_o_g.transform

      def `u-->(u-->g[z])` : (YEF[U] O YEF[U] O G)[Z] =
        tau o v2gv(`z-->z`)

      val yz_2_yu_o_g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
        new:
          def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
            mu o fc.f2a(`z-->__` => (yef o g)(`z-->__`) o `u-->(u-->g[z])`)

      def sigma[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yz_2_yu_o_g.transform

      def f2a[__] = fc.f2a[Arr[Z, __], (YEF[U] O YEF[U] O G)[__]]

      `z-->y` =>
        (tau o v2gv(`z-->y`)) ==:
          // categoryRightIdentityLaw for Arr
          (tau o v2gv(`z-->y` o `z-->z`)) ==:
          // pointfreeYonedaProperty
          (tau o yef(`z-->y`) o v2gv(`z-->z`)) ==:
          // naturalTransformationLaw for tau
          ((yef o g)(`z-->y`) o tau o v2gv(`z-->z`)) ==:
          // definition `u-->(u-->g[z])`
          ((yef o g)(`z-->y`) o `u-->(u-->g[z])`) ==:
          // functionalCategoryMuProperty
          (mu o v2gv((yef o g)((`z-->y`)) o `u-->(u-->g[z])`)) ==:
          // pointfreeApplicationProperty
          (mu o f2a[Y](`z-->y` => (yef o g)(`z-->y`) o `u-->(u-->g[z])`) o v2gv(
            `z-->y`
          )) ==:
          // definition sigma
          (sigma o v2gv(`z-->y`)) ==:
          // done
          qed

  def endoYonedaProof2[Y, X]: (YEF[U] O YEF[U] O G)[Z] => (
      Arr[Y, X] => (Arr[Z, Y] => Proof[(YEF[U] O YEF[U] O G)[X]])
  ) =
    `u-->(u-->g[z])` =>
      `y-->x` =>

        import fc.{v2gv, yef, mu}

        val yz2yu_o_g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
          new:
            def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
              mu o fc.f2a(`z-->__` => (yef o g)(`z-->__`) o `u-->(u-->g[z])`)

        def tau[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yz2yu_o_g.transform

        def f2a[__] = fc.f2a[Arr[Z, __], (YEF[U] O YEF[U] O G)[__]]

        `z-->y` =>
          ((yef o g)(`y-->x`) o tau o v2gv(`z-->y`)) ==:
            // definition tau
            ((yef o g)(`y-->x`) o (mu o f2a[Y](`z-->y` =>
              (yef o g)(`z-->y`) o `u-->(u-->g[z])`
            )) o v2gv(`z-->y`)) ==:
            // pointfreeApplicationProperty
            ((yef o g)(`y-->x`) o (mu o v2gv(
              (yef o g)(`z-->y`) o `u-->(u-->g[z])`
            ))) ==:
            // mu property for (YEF[U], mu, eta)
            ((yef o g)(`y-->x`) o (yef o g)(`z-->y`) o `u-->(u-->g[z])`) ==:
            // functorCompositionProperty for yef o g
            ((yef o g)(`y-->x` o `z-->y`) o `u-->(u-->g[z])`) ==:
            // functionalCategoryMuProperty
            (mu o v2gv((yef o g)(`y-->x` o `z-->y`) o `u-->(u-->g[z])`)) ==:
            // pointfreeApplicationProperty
            (mu o f2a[X](`z-->x` =>
              (yef o g)(`z-->x`) o `u-->(u-->g[z])`
            ) o v2gv(`y-->x` o `z-->y`)) ==:
            // definition tau
            (tau o v2gv(`y-->x` o `z-->y`)) ==:
            // pointfreeYonedaProperty
            (tau o yef(`y-->x`) o v2gv(`z-->y`)) ==:
            qed
