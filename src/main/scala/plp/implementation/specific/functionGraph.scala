package plp.implementation.specific

import plp.specification.{Graph}

type Fun[-Z, +Y] = Z => Y

given functionGraph: Graph[Fun] with {}
