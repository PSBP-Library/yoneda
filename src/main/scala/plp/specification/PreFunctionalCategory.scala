package plp.specification

import plp.notation.{O, I, U}

import plp.implementation.specific.{Fun}

import plp.implementation.generic.{
  identityEndoFunctor,
  Yoneda,
  yonedaFunctor,
  yonedaEndoFunctor
}

trait PreFunctionalCategory[
    Arr[-_, +_]: Category: [_[-_, +_]] =>> Functor[Fun, Arr, I]
] extends Category[Arr]
    with PreTriple[Arr, Yoneda[Arr][U]]:

  def f2a[Z, Y]: Fun[Z, Y] => Arr[Z, Y] = summon[Functor[Fun, Arr, I]].lift

  def v2gv[__]: Fun[__, Arr[U, __]] = __ => f2a(_ => __)

  val etaNaturalTransformation: NaturalTransformation[Arr, Arr, I, YEF[U]] =
    given PreFunctionalCategory[Arr] = this
    new:
      def transform[__]: Arr[I[__], YEF[U][__]] =
        f2a(v2gv)

  type YF = [Z] =>> [__] =>> Yoneda[Arr][Z][__]

  def yf[Z, Y, X]: Arr[Y, X] => Fun[YF[Z][Y], YF[Z][X]] =
    yonedaFunctor[Arr, Z].lift

  type YEF = [Z] =>> [__] =>> Yoneda[Arr][Z][__]

  def yef[Z, Y, X]: Arr[Y, X] => Arr[YEF[Z][Y], YEF[Z][X]] =
    given PreFunctionalCategory[Arr] = this
    yonedaEndoFunctor[Arr, Z].lift

import plp.notation.{Law, =:}

class PreFunctionalCategoryLaws[Arr[-_, +_]: PreFunctionalCategory]:

  import plp.implementation.specific.{functionCategory}

  val pfc = summon[PreFunctionalCategory[Arr]]

  def preFunctionalCategoryFunctorCompositionLaw[Z, Y, X]
      : Fun[Z, Y] => (Fun[Y, X] => Law[Arr[Z, X]]) =
    `z=>y` =>
      `y=>x` =>

        import pfc.{f2a}

        (f2a(`y=>x` o `z=>y`)) =:
          (f2a(`y=>x`) o f2a(`z=>y`))

  def preFunctionalCategoryFunctorIdentityLaw[__]: Law[Arr[__, __]] =

    import functionCategory.{`__-->__` => `__-f->__`}
    
    import pfc.{`__-->__`, f2a}

    f2a(`__-f->__`) =:
      `__-->__`

  import pfc.{YEF}

  def preFunctionalCategoryEtaNaturalTransformationLaw[Z, Y]
      : Arr[Z, Y] => Law[Arr[I[Z], YEF[U][Y]]] =
    `z-->y` =>

      import pfc.{yef, eta}

      val i: Arr[Z, Y] => Arr[Z, Y] = identityEndoFunctor[Arr].lift

      (eta o i(`z-->y`)) =:
        (yef(`z-->y`) o eta)

  def preFunctionalCategoryEtaLaw[__]
      : YEF[U][__] => Law[(YEF[U] O YEF[U])[__]] =
    `u-->__` =>

      import pfc.{eta, v2gv}

      (eta o `u-->__`) =:
        (v2gv(`u-->__`))
