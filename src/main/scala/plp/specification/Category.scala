package plp.specification

trait Category[Arr[-_, +_]] extends Graph[Arr]:

  def composition[Z, Y, X]: (Arr[Y, X], Arr[Z, Y]) => Arr[Z, X]

  def unit[__]: Arr[__, __]

  extension [Z, Y, X](`y-->x`: Arr[Y, X])
    def o(`z-->y`: Arr[Z, Y]): Arr[Z, X] = composition(`y-->x`, `z-->y`)

  def `__-->__`[__]: Arr[__, __] = unit

import plp.notation.{Law, =:}

class CategoryLaws[Arr[-_, +_]: Category]:

  def categoryCompositionAssociativityLaw[Z, Y, X, W]
      : (Arr[Z, Y], Arr[Y, X], Arr[X, W]) => Law[Arr[Z, W]] =
    (`z-->y`, `y-->x`, `x-->w`) =>
      ((`x-->w` o `y-->x`) o `z-->y`) =:
        (`x-->w` o (`y-->x` o `z-->y`))

  def categoryLeftIdentityLaw[Z, Y]: Arr[Z, Y] => Law[Arr[Z, Y]] =
    `z-->y` =>

      val `y-->y` = summon[Category[Arr]].`__-->__`[Y]

      (`y-->y` o `z-->y`) =:
        (`z-->y`)

  def categoryRightIdentityLaw[Z, Y]: Arr[Z, Y] => Law[Arr[Z, Y]] =
    `z-->y` =>

      val `z-->z` = summon[Category[Arr]].`__-->__`[Z]

      (`z-->y` o `z-->z`) =:
        (`z-->y`)
