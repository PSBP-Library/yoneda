package plp.implementation.generic

import plp.specification.{Category, Functor}

import plp.implementation.specific.{Fun, functionCategory}

type Yoneda = [Arr[-_, +_]] =>> [Z] =>> [Y] =>> Arr[Z, Y]

given yonedaFunctor[Arr[-_, +_]: Category, Z]: Functor[Arr, Fun, Yoneda[Arr][Z]]
  with

  type YF = [Z] =>> [__] =>> Yoneda[Arr][Z][__]

  def lift[Y, X]: Arr[Y, X] => Fun[YF[Z][Y], YF[Z][X]] =
    `y-->x` => `z-->y` => `y-->x` o `z-->y`

import plp.notation.{Proof, ==:, qed}

class YonedaFunctorProofs[Z, Arr[-_, +_]: Category]:

  type YF = [Z] =>> [__] =>> Yoneda[Arr][Z][__]

  def yf[Y, X]: Arr[Y, X] => (YF[Z][Y] => YF[Z][X]) = yonedaFunctor.lift

  def compositionProof[Y, X, W]
      : (Arr[Y, X], Arr[X, W]) => YF[Z][Y] => Proof[YF[Z][W]] =
    (`y-->x`, `x-->w`) =>
      `z-->y` =>
        (yf(`x-->w` o `y-->x`)(`z-->y`)) ==:
          // definition yf
          ((`x-->w` o `y-->x`) o `z-->y`) ==:
          // categoryAssociativityLaw for Arr
          (`x-->w` o (`y-->x` o `z-->y`)) ==:
          // definition yf
          (`x-->w` o yf(`y-->x`)(`z-->y`)) ==:
          // definition yf
          (yf(`x-->w`)(yf(`y-->x`)(`z-->y`))) ==:
          // definition o for functionCategory
          ((yf(`x-->w`) o yf(`y-->x`))(`z-->y`)) ==:
          // done
          qed

  def identityProof[Y]: Arr[Z, Y] => Proof[YF[Z][Y]] =
    `z-->y` =>

      val `y-->y` = summon[Category[Arr]].`__-->__`[Y]

      (yf(`y-->y`)(`z-->y`)) ==:
        // definition yf
        (`y-->y` o `z-->y`) ==:
        // categoryLeftIdentityLaw for Arr
        (`z-->y`) ==:
        // done
        qed
