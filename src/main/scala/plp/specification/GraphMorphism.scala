package plp.specification

trait GraphMorphism[Arr_G[-_, +_]: Graph, Arr_H[-_, +_]: Graph, M[+_]]:

  def lift[Z, Y]: Arr_G[Z, Y] => Arr_H[M[Z], M[Y]]
