package plp.notation

case class Law[__](equation: (__, __))

extension [__](lhs: __) def =:(rhs: __): Law[__] = Law(lhs, rhs)
