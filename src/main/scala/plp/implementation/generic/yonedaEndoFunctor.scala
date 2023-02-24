package plp.implementation.generic

import plp.specification.{EndoFunctor, PreFunctionalCategory}

given yonedaEndoFunctor[Arr[-_, +_]: PreFunctionalCategory, Z]
    : EndoFunctor[Arr, Yoneda[Arr][Z]] with

  val pfc = summon[PreFunctionalCategory[Arr]]

  import pfc.{YEF}

  def lift[Y, X]: Arr[Y, X] => Arr[YEF[Z][Y], YEF[Z][X]] =
    `y-->x` =>

      import pfc.{f2a, yf, YEF}
      
      f2a(yf(`y-->x`))
