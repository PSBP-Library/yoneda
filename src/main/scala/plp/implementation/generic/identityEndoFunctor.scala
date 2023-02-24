package plp.implementation.generic

import plp.notation.{I}

import plp.specification.{Category, EndoFunctor}

given identityEndoFunctor[Arr[-_, +_]: Category]: EndoFunctor[Arr, I] with
  def lift[Z, Y]: Arr[Z, Y] => Arr[I[Z], I[Y]] =
    `z-->y` => `z-->y`

import plp.notation.{Proof, ==:, qed}

class IdentityEndoFunctorProofs[Arr[-_, +_]: Category]:

  def i[Z, Y]: Arr[Z, Y] => Arr[Z, Y] = identityEndoFunctor.lift

  def functorCompositionProof[Z, Y, X]
      : Arr[Z, Y] => (Arr[Y, X] => Proof[Arr[I[Z], I[X]]]) =
    `z-->y` =>
      `y-->x` =>
        (i(`y-->x` o `z-->y`)) ==:
          // definition i
          identity(`y-->x` o `z-->y`) ==:
          // definition identity
          (`y-->x` o `z-->y`) ==:
          // definition identity
          (identity(`y-->x`) o identity(`z-->y`)) ==:
          // definition i
          (i(`y-->x`) o i(`z-->y`)) ==:
          // done
          qed

  def functorIdentityProof[Z]: Proof[Arr[I[Z], I[Z]]] =

    val `z-->z` = summon[Category[Arr]].`__-->__`[Z]

    (i(`z-->z`)) ==:
      // definition i
      (identity(`z-->z`)) ==:
      // definition identity
      (`z-->z`) ==:
      // done
      qed
