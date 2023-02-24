package plp.specification

import plp.notation.{O}

trait Triple[Arr[-_, +_]: Category, T[+_]: [_[+_]] =>> EndoFunctor[Arr, T]]
    extends PreTriple[Arr, T]:

  def t[Z, Y]: Arr[Z, Y] => Arr[T[Z], T[Y]] = summon[EndoFunctor[Arr, T]].lift

  val muNaturalTransformation: NaturalTransformation[Arr, Arr, T O T, T]

  def mu[__]: Arr[(T O T)[__], T[__]] = muNaturalTransformation.transform

import plp.notation.{Law, =:}

class TripleLaws[Arr[-_, +_]: Category, T[+_]: [_[+_]] =>> Triple[Arr, T]]:

  val c: Category[Arr] = summon[Category[Arr]]

  import c.{o, unit => upsilon}

  val triple: Triple[Arr, T] = summon[Triple[Arr, T]]

  import triple.{t, eta, mu}

  def tripleLeftIdentityLaw[__]: Law[Arr[T[__], T[__]]] =
    (mu o eta[T[__]]) =:
      (upsilon)

  def tripleRightIdentityLaw[__]: Law[Arr[T[__], T[__]]] =    
    (mu o t(eta)) =:
      (upsilon)

  def tripleAssociativityLaw[__]: Law[Arr[(T O T O T)[__], T[__]]] =
    (mu o mu[T[__]]) =:
      (mu o t(mu))
