module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexTwoEndpointPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCochainHomotopy
public import SerrePositivity.InfinityCategories.Core.OuterHornConverse

/-! 同じ path primitive の負号から、始点から終点への全単体ホモトピーを構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] (Q : Complex R)

lemma dgGluingComplexPathNegativePrimitive_boundary :
    δ (-1) 0 (-dgGluingComplexPathPrimitive Q) =
      Cochain.ofHom (dgGluingComplexPathEnd Q - dgGluingComplexPathStart Q) := by
  rw [δ_neg, eq_neg_of_add_eq_zero_left (dgGluingComplexPathPrimitive_boundary Q), neg_neg]

def dgGluingComplexPathSpaceHomotopy :
    SSet.Homotopy (complexPinchedMap.{u, v} (dgGluingComplexPathStart Q))
      (complexPinchedMap.{u, v} (dgGluingComplexPathEnd Q)) :=
  dgGluingComplexPinchedHomotopy_of_cochain _ _ (-dgGluingComplexPathPrimitive Q)
    (dgGluingComplexPathNegativePrimitive_boundary Q)

lemma dgGluingComplexPathSpaceHomotopy_invertible :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (dgGluingComplexPathSpaceHomotopy.{u, v} Q)) := by
  exact isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)

end SerrePositivity.InfinityCategories
