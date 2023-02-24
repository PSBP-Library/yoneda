package plp.implementation.specific

import plp.notation.{O, I, U, u}

import plp.specification.{FunctionalCategory, NaturalTransformation}

import plp.implementation.generic.{
  identityEndoFunctor,
  composedFunctor,
  yonedaEndoFunctor
}

given functionFunctionalCategory: FunctionalCategory[Fun] with
  def composition[Z, Y, X]: (Fun[Y, X], Fun[Z, Y]) => Fun[Z, X] =
    functionCategory.composition

  def unit[Z]: Fun[Z, Z] = functionCategory.unit

  def lift[Z, Y]: Fun[Z, Y] => Fun[I[Z], I[Y]] = identityEndoFunctor.lift

  val muNaturalTransformation
      : NaturalTransformation[Fun, Fun, YEF[U] O YEF[U], YEF[U]] =
    new:
      def transform[__]: Fun[(YEF[U] O YEF[U])[__], YEF[U][__]] =
        `u-->(u-->__)` => `u-->(u-->__)`(u)

import plp.notation.{Proof, ==:, qed}

import plp.implementation.specific.{functionCategory}

class FunctionFunctionalCategoryProofs:

  def functionPreFunctionalCategoryFunctorCompositionProof[Z, Y, X]
      : Fun[Z, Y] => (Fun[Y, X] => Proof[Fun[Z, X]]) =
    `z=>y` =>
      `y=>x` =>

        import functionFunctionalCategory.{f2a}

        f2a(`y=>x` o `z=>y`) ==:
          // definition f2a for identityEndoFunctor for Fun
          (`y=>x` o `z=>y`) ==:
          // definition f2a for identityEndoFunctor for Fun
          (f2a(`y=>x`) o f2a(`z=>y`)) ==:
          // done
          qed

  def functionPreFunctionalCategoryFunctorIdentityProof[__]
      : Proof[Fun[__, __]] =

    import functionCategory.{`__-->__`}

    import functionFunctionalCategory.{f2a}

    f2a(`__-->__`) ==:
      // definition f2a for identityEndoFunctor for Fun
      `__-->__` ==:
      // done
      qed

  import functionFunctionalCategory.{YEF}

  def functionPreFunctionalCategoryEtaNaturalTransformationProof[Z, Y]
      : Fun[Z, Y] => Proof[Fun[I[Z], YEF[U][Y]]] =
    `z=>y` =>

      import functionFunctionalCategory.{o, f2a, v2gv, yf, yef, eta}

      def i[Z, Y]: Fun[Z, Y] => Fun[Z, Y] = identityEndoFunctor.lift

      (yef(`z=>y`) o eta) ==:
        // definition eta for functionFunctionalCategory
        (yef(`z=>y`) o f2a(v2gv)) ==:
        // definition f2a for identityEndoFunctor for Fun
        (yef(`z=>y`) o v2gv) ==:
        // definition v2gv
        (yef(`z=>y`) o ((z: Z) => f2a(_ => z))) ==:
        // definition f2a for identityEndoFunctor for Fun
        (yef(`z=>y`) o ((z: Z) => (_ => z))) ==:
        // definition yef
        (f2a(yf(`z=>y`)) o ((z: Z) => (_ => z))) ==:
        // definition f2a for identityEndoFunctor for Fun
        (yf(`z=>y`) o ((z: Z) => (_ => z))) ==:
        // definition o for functionCategory
        ((z: Z) => yf(`z=>y`)(_ => z)) ==:
        // definition yf
        ((z: Z) => (`z=>y` o (_ => z))) ==:
        // definition o for functionCategory
        ((z: Z) => (_: U) => `z=>y`(z)) ==:
        // definition definition o for functionCategory (substituting `z=>y`(z) for y)
        (((y: Y) => (_: U) => y) o (z => `z=>y`(z))) ==:
        // lambda calculus eta conversion
        (((y: Y) => ((_: U) => y)) o `z=>y`) ==:
        // definition f2a for identityEndoFunctor for Fun
        (((y: Y) => f2a(_ => y)) o `z=>y`) ==:
        // definition v2gv
        (v2gv o `z=>y`) ==:
        // definition f2a for identityEndoFunctor for Fun
        (f2a(v2gv) o `z=>y`) ==:
        // definition eta
        (eta o `z=>y`) ==:
        // definition i
        (eta o i(`z=>y`)) ==:
        // done
        qed

  def functionFunctionalCategoryMuNaturalTransformationProof[Z, Y]
      : Fun[Z, Y] => Proof[(YEF[U] O YEF[U])[Z] => YEF[U][Y]] =
    `z=>y` =>

      import functionFunctionalCategory.{o, f2a, yf, yef, mu}

      (yef(`z=>y`) o mu) ==:
        // definition yef
        (f2a(yf(`z=>y`)) o mu) ==:
        // definition f2a for identityEndoFunctor for Fun
        (yf(`z=>y`) o mu) ==:
        // definition mu for functionFunctionalCategory
        (yf(`z=>y`) o (_(u))) ==:
        // definition o for functionCategory
        (`u=>(u=>z)` => yf(`z=>y`)(`u=>(u=>z)`(u))) ==:
        // definition yf
        (`u=>(u=>z)` => (`z=>y` o `u=>(u=>z)`(u))) ==:
        // eta conversion lambda calculus
        (
            (
                (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) =>
                  ((u: U) => (`z=>y` o `u=>(u=>z)`(u)))(u)
              )
        ) ==:
        // definition o for functionCategory
        (((`u=>(u=>y)`: (YEF[U] O YEF[U])[Y]) => `u=>(u=>y)`(u)) o (
          (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => (u => `z=>y` o `u=>(u=>z)`(u))
        )) ==:
        // definition o for functionCategory
        (((`u=>(u=>y)`: (YEF[U] O YEF[U])[Y]) => `u=>(u=>y)`(u)) o (
          (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) =>
            ((`u=>z`: YEF[U][Z]) => `z=>y` o `u=>z`) o (u => `u=>(u=>z)`(u))
        )) ==:
        // eta conversion lambda calculus
        (((`u=>(u=>y)`: (YEF[U] O YEF[U])[Y]) => `u=>(u=>y)`(u)) o (
          (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) =>
            ((`u=>z`: YEF[U][Z]) => `z=>y` o `u=>z`) o `u=>(u=>z)`
        )) ==:
        // // definition yf
        (((`u=>(u=>y)`: (YEF[U] O YEF[U])[Y]) => `u=>(u=>y)`(u)) o yf(
          (`u=>z`: YEF[U][Z]) => `z=>y` o `u=>z`
        )) ==:
        // definition yf
        (((`u=>(u=>y)`: (YEF[U] O YEF[U])[Y]) => `u=>(u=>y)`(u)) o yf(
          yf(`z=>y`)
        )) ==:
        // definition mu for functionFunctionalCategory
        (mu o yf(yf(`z=>y`))) ==:
        // definition f2a for identityEndoFunctor for Fun
        (mu o f2a(yf(f2a(yf(`z=>y`))))) ==:
        // definition yef
        (mu o yef(yef(`z=>y`))) ==:
        // done
        qed

  def functionFunctionalCategoryEtaProof[Z]
      : YEF[U][Z] => Proof[(YEF[U] O YEF[U])[Z]] =
    `u=>z` =>

      import functionFunctionalCategory.{o, f2a, v2gv, eta}

      (eta o `u=>z`) ==:
        // definition eta for functionFunctionalCategory
        (f2a(v2gv) o `u=>z`) ==:
        // definition f2a for identityEndoFunctor for Fun
        (v2gv o `u=>z`) ==:
        // definition v2gv
        (((z: Z) => f2a(_ => z)) o `u=>z`) ==:
        // definition f2a for identityEndoFunctor
        (((z: Z) => ((_: U) => z)) o `u=>z`) ==:
        // eta conversion lambda calculus
        (((z: Z) => ((_: U) => z)) o (u => `u=>z`(u))) ==:
        // definition o for functionCategory
        (u => ((_: U) => `u=>z`(u))) ==:
        // eta conversion lambda calculus
        (_ => `u=>z`) ==:
        // definition f2a for identityEndoFunctor for Fun
        (f2a(_ => `u=>z`)) ==:
        // definition v2gv
        v2gv(`u=>z`) ==:
        // done
        qed

  def functionFunctionalCategoryTripleLeftIdentityProof[Z]
      : Proof[YEF[U][Z] => YEF[U][Z]] =

    import functionFunctionalCategory.{unit, f2a, v2gv, eta, mu}

    def upsilon[__] = unit[__]

    (mu o eta) ==:
      // definition eta for functionFunctionalCategory
      (mu o f2a(v2gv)) ==:
      // definition f2a for identityEndoFunctor for Fun
      (mu o v2gv) ==:
      // definition v2gv
      (mu o (`u=>z` => f2a(_ => `u=>z`))) ==:
      // definition f2a for identityEndoFunctor for Fun
      (mu o (`u=>z` => (_ => `u=>z`))) ==:
      // definition mu for functionFunctionalCategory
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o (`u=>z` =>
        (_ => `u=>z`)
      )) ==:
      // definition o for functionCategory
      ((`u=>z` => ((_: U) => `u=>z`)(u))) ==:
      // lambda calculus eta conversion (U has only one value, u)
      (`u=>z` => `u=>z`) ==:
      // definition unit for Fun
      unit ==:
      // definition upsilon
      upsilon[YEF[U][Z]] ==:
      // done
      qed

  def functionFunctionalCategoryTripleRightIdentityProof[Z]
      : Proof[YEF[U][Z] => YEF[U][Z]] =

    import functionFunctionalCategory.{unit, f2a, v2gv, yef, yf, eta, mu}

    def upsilon[__] = unit[__]

    (mu o yef(eta)) ==:
      // definition yef
      (mu o f2a(yf(eta))) ==:
      // definition f2a for identityEndoFunctor for Fun
      (mu o yf(eta)) ==:
      // definition eta for functionFunctionalCategory
      (mu o yf(f2a(v2gv))) ==:
      // definition f2a for identityEndoFunctor for Fun
      (mu o yf(v2gv)) ==:
      // definition v2gv
      (mu o yf(f2a(z => (_ => z)))) ==:
      // definition f2a for identityEndoFunctor for Fun
      (mu o yf(z => _ => z)) ==:
      // definition mu for functionFunctionalCategory
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o yf(z =>
        (_ => z)
      )) ==:
      // definition yf
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o (`u=>z` =>
        ((z: Z) => ((_: U) => z)) o `u=>z`
      )) ==:
      // definition o for functionCategory
      (`u=>z` => (((z: Z) => ((_: U) => z)) o `u=>z`)(u)) ==:
      // definition o for functionCategory
      (`u=>z` => (_ => `u=>z`(u))) ==:
      // lambda calculus eta conversion (U has only one value, u)
      (`u=>z` => `u=>z`) ==:
      // definition unit for Fun
      unit ==:
      // definition upsilon
      upsilon[YEF[U][Z]] ==:
      // done
      qed

  def functionFunctionalCategoryTripleAssociativityProof[Z]
      : Proof[(YEF[U] O YEF[U] O YEF[U])[Z] => YEF[U][Z]] =

    import functionFunctionalCategory.{f2a, yf, yef, mu}

    (mu o mu) ==:
      // definition mu for functionFunctionalCategory
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o (
        (`u=>(u=>(u=>z))`: (YEF[U] O YEF[U] O YEF[U])[Z]) => `u=>(u=>(u=>z))`(u)
      )) ==:
      // definition o for functionCategory
      (
          (
              (`u=>(u=>(u=>z))`: (YEF[U] O YEF[U] O YEF[U])[Z]) =>
                `u=>(u=>(u=>z))`(u)(u)
            )
      ) ==:
      // definition o for functionCategory
      (
          (
              (`u=>(u=>(u=>z))`: (YEF[U] O YEF[U] O YEF[U])[Z]) =>
                ((
                    (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)
                ) o `u=>(u=>(u=>z))`)(u)
            )
      ) ==:
      // definition o for functionCategory
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o (
        (`u=>(u=>(u=>z))`: (YEF[U] O YEF[U] O YEF[U])[Z]) =>
          (
              (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)
          ) o `u=>(u=>(u=>z))`
      )) ==:
      // definition yf
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o yf(
        (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)
      )) ==:
      // definition f2a for identityEndoFunctor
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o f2a(
        yf((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u))
      )) ==:
      // definition yef
      (((`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)) o yef(
        (`u=>(u=>z)`: (YEF[U] O YEF[U])[Z]) => `u=>(u=>z)`(u)
      )) ==:
      // definition mu for functionFunctionalCategory
      (mu o yef(mu)) ==:
      // done
      qed
