package plp.notation

import scala.collection.immutable.Seq

case class Proof[__](steps: Seq[__])

extension [__](step: __)
  def ==:(proof: Proof[__]): Proof[__] = Proof(step +: proof.steps)

def qed[__]: Proof[__] = Proof(Seq())
