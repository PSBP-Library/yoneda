package plp.proposition

import plp.notation.{O, U, Law, =:}

import plp.specification.{
  PreFunctionalCategory,
  EndoFunctor,
  NaturalTransformation
}

import plp.implementation.generic.{composedFunctor, yonedaEndoFunctor}

import plp.implementation.specific.{functionCategory}

class PreFunctionalCategoryEndoYonedaLemma[
    Z,
    Arr[-_, +_]: PreFunctionalCategory,
    G[+_]: [G[+_]] =>> EndoFunctor[Arr, G]
]:

  val pfc = summon[PreFunctionalCategory[Arr]]

  import pfc.{YEF}

  def g[Z, Y]: Arr[Z, Y] => Arr[G[Z], G[Y]] = summon[EndoFunctor[Arr, G]].lift

  def endoYonedaLemma1[Y]: NaturalTransformation[Arr, Arr, YEF[Z], G] => Law[
    Arr[YEF[Z][Y], (YEF[U] O G)[Y]]
  ] =
    yefz2g =>

      import pfc.{`__-->__`, v2gv, eta}

      val `z-->z` = `__-->__`[Z]

      def tau[__]: Arr[YEF[Z][__], G[__]] = yefz2g.transform

      val `u-->g[z]` : (YEF[U] O G)[Z] =
        tau o v2gv(`z-->z`)

      val yefz_2_g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
        new:
          def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
            pfc.f2a(`z--> __` => g(`z--> __`) o `u-->g[z]`)

      def sigma[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
        yefz_2_g.transform

      (eta[G[Y]] o tau) =:
        sigma

  def endoYonedaLemma2[Y, X]
      : (YEF[U] O G)[Z] => (Arr[Y, X] => Law[Arr[YEF[Z][Y], (YEF[U] O G)[X]]]) =
    `u-->g[z]` =>
      `y-->x` =>

        import pfc.{yef}

        val yefz2g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
          new:
            def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
              pfc.f2a(`z--> __` => g(`z--> __`) o `u-->g[z]`)

        def tau[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yefz2g.transform

        ((yef o g)(`y-->x`) o tau) =:
          (tau o yef(`y-->x`))

import plp.notation.{Proof, ==:, qed}

class PreFunctionalCategoryEndoYonedaProofs[
    Z,
    Arr[-_, +_]: PreFunctionalCategory,
    G[+_]: [G[+_]] =>> EndoFunctor[Arr, G]
]:

  val pfc = summon[PreFunctionalCategory[Arr]]

  import pfc.{YEF}

  def g[Z, Y]: Arr[Z, Y] => Arr[G[Z], G[Y]] = summon[EndoFunctor[Arr, G]].lift

  def endoYonedaProof1[Y]: NaturalTransformation[Arr, Arr, YEF[Z], G] => (
      Arr[Z, Y] => Proof[(YEF[U] O YEF[U] O G)[Y]]
  ) =
    yefz2g =>

      import pfc.{`__-->__`, v2gv, yef, eta}

      val `z-->z` = `__-->__`[Z]

      def tau[__]: Arr[YEF[Z][__], G[__]] = yefz2g.transform

      val `u-->g[z]` : (YEF[U] O G)[Z] =
        tau o v2gv(`z-->z`)

      val yefz_2_g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
        new:
          def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
            pfc.f2a(`z--> __` => g(`z--> __`) o `u-->g[z]`)

      def sigma[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
        yefz_2_g.transform

      def f2a[__] = pfc.f2a[Arr[Z, __], (YEF[U] O G)[__]]

      `z-->y` =>
        (eta[G[Y]] o tau o v2gv(`z-->y`)) ==:
          // categoryRightIdentityLaw for Arr
          (eta o tau o v2gv(`z-->y` o `z-->z`)) ==:
          // pointfreeYonedaProperty
          (eta o tau o yef(`z-->y`) o v2gv(`z-->z`)) ==:
          // naturalTransformationLaw for eta o tau
          ((yef o g)(`z-->y`) o eta o tau o v2gv(`z-->z`)) ==:
          // definition `u-->g[z]`
          ((yef o g)(`z-->y`) o eta o `u-->g[z]`) ==:
          // preFunctionalCategoryEtaLaw
          ((yef o g)(`z-->y`) o v2gv(`u-->g[z]`)) ==:
          // definition o for functionCategory
          ((yef(g(`z-->y`)) o v2gv(`u-->g[z]`))) ==:
          // pointfreeYonedaProperty
          (v2gv(g(`z-->y`) o `u-->g[z]`)) ==:
          // pointfreeApplicationProperty
          (f2a[Y](`z--> __` => g(`z--> __`) o `u-->g[z]`) o v2gv(`z-->y`)) ==:
          // definition sigma
          (sigma o v2gv(`z-->y`)) ==:
          // done
          qed

  def endoYonedaProof2[Y, X]: (YEF[U] O G)[Z] => (
      Arr[Y, X] => (Arr[Z, Y] => Proof[(YEF[U] O YEF[U] O G)[X]])
  ) =
    `u-->g[z]` =>
      `y-->x` =>

        import pfc.{v2gv, yef}

        val yefz2g: NaturalTransformation[Arr, Arr, YEF[Z], YEF[U] O G] =
          new:
            def transform[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] =
              pfc.f2a(`z--> __` => g(`z--> __`) o `u-->g[z]`)

        def tau[__]: Arr[YEF[Z][__], (YEF[U] O G)[__]] = yefz2g.transform

        def f2a[__] = pfc.f2a[Arr[Z, __], (YEF[U] O G)[__]]

        `z-->y` =>
          ((yef o g)(`y-->x`) o tau o v2gv(`z-->y`)) ==:
            // definition tau
            ((yef o g)(`y-->x`) o f2a[Y](`z--> __` =>
              g(`z--> __`) o `u-->g[z]`
            ) o v2gv(`z-->y`)) ==:
            // pointfreeApplicationProperty
            ((yef o g)(`y-->x`) o v2gv(g(`z-->y`) o `u-->g[z]`)) ==:
            // definition o for functionCategory
            (yef(g(`y-->x`)) o v2gv(g(`z-->y`) o `u-->g[z]`)) ==:
            // pointfreeYonedaProperty
            v2gv(g(`y-->x`) o g(`z-->y`) o `u-->g[z]`) ==:
            // functorCompositionLaw for g
            v2gv(g(`y-->x` o `z-->y`) o `u-->g[z]`) ==:
            // pointfreeApplicationProperty
            (f2a[X](`z--> __` => g(`z--> __`) o `u-->g[z]`) o v2gv(
              `y-->x` o `z-->y`
            )) ==:
            // definition tau
            (tau o v2gv(`y-->x` o `z-->y`)) ==:              
            // pointfreeYonedaProperty
            (tau o yef(`y-->x`) o v2gv(`z-->y`)) ==:
            // done
            qed
