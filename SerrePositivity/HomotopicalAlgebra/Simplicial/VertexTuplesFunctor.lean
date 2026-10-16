module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.VertexTuples

/-! # Ordered tuple spaces and strict vertex inclusions as actual functors -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.VertexTuples

def tupleFunctor : Type v ⥤ SSet.{v} where
  obj := obj
  map f := map f

def vertexFunctor : Type v ⥤ SSet.{v} where
  obj := vertices
  map f := verticesMap f

def inclusionNatTrans : vertexFunctor ⟶ tupleFunctor where
  app := inclusion
  naturality {_ _} f := (inclusion_map f).symm

end SerrePositivity.SimplicialModel.VertexTuples
