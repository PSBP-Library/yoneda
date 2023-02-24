package plp.proposition

import plp.notation.{U, u, Law, =:}

import plp.specification.{PreFunctionalCategory}

import plp.implementation.specific.{Fun}

class PreFunctionalCategoryProperties[Arr[-_, +_]: PreFunctionalCategory]:

  val pfc = summon[PreFunctionalCategory[Arr]]

  import pfc.{YEF}

  def pointfreeApplicationProperty[Z, Y]: Fun[Z, Y] => (Z => Law[YEF[U][Y]]) =
    `z=>y` =>
      z =>

        import pfc.{v2gv, f2a}

        (f2a(`z=>y`) o v2gv(z)) =:
          (v2gv(`z=>y`(z)))

  def pointfreeYonedaProperty[Z, Y, X]
      : Arr[Z, Y] => (Arr[Y, X] => Law[YEF[U][Arr[Z, X]]]) =
    `z-->y` =>
      `y-->x` =>

        import pfc.{v2gv, yef}

        (yef(`y-->x`) o v2gv(`z-->y`)) =:
          (v2gv(`y-->x` o `z-->y`))

import plp.notation.{Proof, ==:, qed}

import plp.implementation.specific.{functionCategory}

class PreFunctionalCategoryProofs[Z, Arr[-_, +_]: PreFunctionalCategory]:

  val pfc = summon[PreFunctionalCategory[Arr]]

  import pfc.{YEF}

  def pointfreeApplicationProof[Z, Y]: Fun[Z, Y] => (Z => Proof[YEF[U][Y]]) =
    `z=>y` =>
      z =>

        import pfc.{f2a, v2gv}

        (f2a(`z=>y`) o v2gv(z)) ==:
          // definition v2gv
          (f2a(`z=>y`) o f2a(_ => z)) ==:
          // functorCompositionLaw for f2a
          (f2a(`z=>y` o (_ => z))) ==:
          // definition o for functionCategory
          (f2a(_ => `z=>y`(z))) ==:
          // definition v2gv
          (v2gv(`z=>y`(z))) ==:
          // done
          qed

  def pointfreeYonedaProof[Y, X]
      : Arr[Z, Y] => (Arr[Y, X] => Proof[YEF[U][Arr[Z, X]]]) =
    `z-->y` =>
      `y-->x` =>

        import pfc.{yf, yef, v2gv}

        def f2a[__] = pfc.f2a[Arr[__, Y], Arr[__, X]]

        (yef(`y-->x`) o v2gv(`z-->y`)) ==:
          // definition yef and definition f2a
          (f2a[Z](yf(`y-->x`)) o v2gv(`z-->y`)) ==:
          // definition yf
          (f2a[Z](`z-->y` => `y-->x` o `z-->y`) o v2gv(`z-->y`)) ==:
          // pointfreeApplicationProperty and definition f2a
          (v2gv(`y-->x` o `z-->y`)) ==:
          // done
          qed
