package plp.specification

import plp.notation.{U}

import plp.implementation.generic.{Yoneda}

trait FunctionalCategory[Arr[-_, +_]: Category]
    extends PreFunctionalCategory[Arr]
    with Triple[Arr, Yoneda[Arr][U]]

import plp.notation.{O, Law, =:}

import plp.implementation.specific.{functionCategory}

class FunctionalCategoryLaws[Arr[-_, +_]: FunctionalCategory]:

  val fc = summon[FunctionalCategory[Arr]]

  import fc.{YEF}

  def functionalCategoryMuNaturalTransformationLaw[Z, Y]
      : Arr[Z, Y] => Law[Arr[(YEF[U] O YEF[U])[Z], YEF[U][Y]]] =
    `z-->y` =>

      import fc.{yef, mu}

      (mu o (yef o yef)(`z-->y`)) =:
        (yef(`z-->y`) o mu)

  def functionalCategoryTripleLeftIdentityLaw[__]: Law[Arr[YEF[U][__], YEF[U][__]]] =

    import fc.{unit => upsilon, eta, mu}

    (mu o eta) =:
      (upsilon)

  def functionalCategoryTripleRightIdentityLaw[__]: Law[Arr[YEF[U][__], YEF[U][__]]] =

    import fc.{unit => upsilon, yef, eta, mu}

    (mu o yef(eta)) =:
      (upsilon)

  def functionalCategoryTripleAssociativityLaw[__]
      : Law[Arr[(YEF[U] O YEF[U] O YEF[U])[__], YEF[U][__]]] =

    import fc.{yef, mu}

    (mu o mu) =:
      (mu o yef(mu))
