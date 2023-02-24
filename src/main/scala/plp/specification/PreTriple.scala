package plp.specification

import plp.notation.{I}

trait PreTriple[
    Arr[-_, +_]: Category,
    PT[+_]: [_[+_]] =>> EndoFunctor[Arr, PT]
]:

  val etaNaturalTransformation: NaturalTransformation[Arr, Arr, I, PT]

  def eta[__]: Arr[I[__], PT[__]] = etaNaturalTransformation.transform
