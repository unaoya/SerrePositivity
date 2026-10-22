module

public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementOriginalIsos

/-!
概要：元の精密化を反転して持ち上げた同じ実辺の類を保持する。
方針：元の Kan Hom の反転の Kan 性で同じ類を同型にする。
規約：逆辺を選ばない。使われ方：左 Hom 全係数比較の元の精密化に沿う自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定精密化の反転を持ち上げた同じ辺の類の同型。 -/
def coherentKanOppositeRefinementIso (K L : KanObject.{u})
    (e : (SimplicialCategory.sHom K L) _⦋1⦌) :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)
      (ULift.up (SSet.opObjEquiv.symm ((SimplicialCategory.sHom K L).δ 0 e)))
      (ULift.up (SSet.opObjEquiv.symm ((SimplicialCategory.sHom K L).δ 1 e))) := by
  let c := SSet.Edge.ofTruncated
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)
    (uliftTruncatedEdge.{u, u + 1} (edgeOp (edgeOfSimplex e)))
  have : IsInvertibleEdge
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)
      c.toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk c.toTruncated)

end SerrePositivity.InfinityCategories.F2
