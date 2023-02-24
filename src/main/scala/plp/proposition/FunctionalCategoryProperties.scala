package plp.proposition

import plp.notation.{O, U, Law, =:}

import plp.specification.{FunctionalCategory}

class FunctionalCategoryProperties[Z, Arr[-_, +_]: FunctionalCategory]:

  val fc = summon[FunctionalCategory[Arr]]

  import fc.{YEF}

  def functionalCategoryMuProperty[__]
      : (YEF[U] O YEF[U])[__] => Law[(YEF[U] O YEF[U])[__]] =
    `u-->(u-->__)` =>

      import fc.{v2gv, mu}

      (mu o v2gv(`u-->(u-->__)`)) =:
        (`u-->(u-->__)`)

import plp.notation.{Proof, ==:, qed}

class FunctionalCategoryProoof[Z, Arr[-_, +_]: FunctionalCategory]:

  val fc = summon[FunctionalCategory[Arr]]

  import fc.{YEF}

  def functionalCategoryMuProof[__]
      : (YEF[U] O YEF[U])[__] => Proof[(YEF[U] O YEF[U])[__]] =
    `u-->(u-->__)` =>

      import fc.{unit, v2gv, eta, mu}

      def upsilon[__] = unit[__]

      (mu o v2gv(`u-->(u-->__)`)) ==:
        // preFunctionalCategoryEtaLaw for YEF[U]
        (mu o (eta o `u-->(u-->__)`)) ==:
        // categoryCompositionAssociativityLaw for Arr
        ((mu o eta) o `u-->(u-->__)`) ==:
        // tripleLeftIdentityLaw for YEF[U]
        (`u-->(u-->__)` o upsilon) ==:
        // definition upsilon
        (`u-->(u-->__)` o unit) ==:
        // categoryRightIdentityLaw for Arr
        (`u-->(u-->__)`) ==:
        qed
