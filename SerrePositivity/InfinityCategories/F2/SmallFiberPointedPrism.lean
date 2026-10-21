module

public import SerrePositivity.InfinityCategories.F2.PointedSimplexSourceRestriction
public import SerrePositivity.InfinityCategories.F2.CoherentNativeTriangleSections
public import SerrePositivity.InfinityCategories.F2.CoherentTriangleDiagramEndpoints

/-!
概要：元の coherent 変換の普遍 prism を、元の小さい始域 fiber の全族へ制限する。
方針：縮小の同型と fiber 包含で同じ普遍 prism を前合成する。
規約：元の変換と全円柱を保持。使われ方：実際の fiber 射を表す辺上の切断族の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "w" => unstraighteningMappingFamilyWitness F G (SSet.const x)

/-- 元の変換を元の底の点で評価した同じ図式辺。 -/
def coherentTransformationPointEdge : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  coherentTransformationPointDiagram (coherentTransformationFamilyDiagram (SSet.const x))
    (ULift.up b)

/-- 元の普遍 prism を、同じ小さい始域 fiber の全パラメータで制限した全族。 -/
def coherentSmallFiberPointedPrism : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ PointedSpaceInfinity.{u} :=
  (Δ[1] ◁ lift (m).left (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ (w).leftPrism

/-- 全 prism は元の変換の同じ一点評価の辺を被覆する。 -/
lemma coherentSmallFiberPointedPrism_projection :
    coherentSmallFiberPointedPrism F G x b ≫ pointedSpaceProjection =
      fst Δ[1] a ≫ coherentTransformationPointEdge F G x b :=
  pointedSimplexSourceRestriction_projection (leftUnstraighteningProjection F) (ULift.up b)
    (m).left (smallFiberSourceRestriction_projection F b) _ _ (w).leftPrism_projection

/-- 元の辺の始点は元の同じ始域値である。 -/
lemma coherentTransformationPointEdge_source :
    (coherentTransformationPointEdge F G x b).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 0) = F.app _ (ULift.up b) := by
  rw [coherentTransformationPointEdge, coherentTransformationPointDiagram_edge]
  exact edgeSimplex_source_value (functorEdgeAt (intervalMappingEdgeOfVertex x) (ULift.up b))

/-- 元の辺の終点は元の同じ標的値である。 -/
lemma coherentTransformationPointEdge_target :
    (coherentTransformationPointEdge F G x b).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm 1) = G.app _ (ULift.up b) := by
  rw [coherentTransformationPointEdge, coherentTransformationPointDiagram_edge]
  exact edgeSimplex_target_value (functorEdgeAt (intervalMappingEdgeOfVertex x) (ULift.up b))

end SerrePositivity.InfinityCategories.F2
