package plp.implementation.specific

import plp.specification.{Category}

given functionCategory: Category[Fun] with
  def composition[Z, Y, X]: (Fun[Y, X], Fun[Z, Y]) => Fun[Z, X] =
    (`y=>x`, `z=>y`) => z => `y=>x`(`z=>y`(z))

  def unit[__]: Fun[__, __] = __ => __

import plp.notation.{Proof, ==:, qed}

class FunctionCategoryProofs:

  def functionCompositionAssociativityProof[Z, Y, X, W]
      : ((Fun[Z, Y], Fun[Y, X], Fun[X, W]) => Z => Proof[W]) =
    (`z=>y`, `y=>x`, `x=>w`) =>
      z =>
        ((`x=>w` o `y=>x`) o `z=>y`)(z) ==:
          // definition o for Fun
          (`x=>w` o `y=>x`)(`z=>y`(z)) ==:
          // definition o for Fun
          `x=>w`(`y=>x`(`z=>y`(z))) ==:
          // definition o for Fun
          `x=>w`((`y=>x` o `z=>y`)(z)) ==:
          // definition o for Fun
          (`x=>w` o (`y=>x` o `z=>y`))(z) ==:
          // done
          qed

  def functionLeftIdentityProof[Z, Y]: Fun[Z, Y] => Z => Proof[Y] =
    `z=>y` =>
      z =>

        val `y-->y` = functionCategory.`__-->__`[Y]

        (`y-->y` o `z=>y`)(z) ==:
          // definition o for Fun
          `y-->y`(`z=>y`(z)) ==:
          // definition `y-->y` for Fun
          (`z=>y`) (z) ==:
          // done
          qed

  def functionRightIdentityProof[Z, Y]: Fun[Z, Y] => Z => Proof[Y] =
    `z=>y` =>
      z =>

        val `z-->z` = functionCategory.`__-->__`[Z]

        (`z=>y` o `z-->z`)(z) ==:
          // definition o for Fun
          `z=>y`(`z-->z`(z)) ==:
          // definition `z-->z` for Fun
          (`z=>y`) (z) ==:
          // done
          qed
