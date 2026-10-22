module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingVertexRecovery

/-!
概要：元の写像空間の指定頂点に対応する、選択済みの実際の unstraightening prism。
方針：元の普遍持ち上げを同じ指定頂点へ制限し、始点・終点・底を計算する。
規約：別の変換や別の終点写像を選ばず、元の比較射の値そのものを回収。
使われ方：元の余錐の指定 fiber 写像を、同じ全余錐上の prism として比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)

/-- 普遍的な変換の族を指定頂点で評価すると、同じ元の変換の prism を回収する。 -/
lemma unstraighteningTransformationFamily_at_vertex :
    lift (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ B)) (SSet.const x) ≫
      leftUnstraighteningTransformationFamily F G =
      functorEdgePrism (intervalMappingEdgeOfVertex x) := by
  have h := leftUnstraighteningTransformationFamily_at_edge F G (intervalMappingEdgeOfVertex x)
  have he : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex x) = x :=
    (intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).apply_symm_apply x
  rw [he] at h
  exact h

/-- 指定頂点に対する元の普遍持ち上げの制限。 -/
def unstraighteningVertexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u} :=
  lift (𝟙 _) (SSet.const x) ≫ leftUnstraighteningTransformationFamilyLift F G

/-- 同じ制限の始点は、元の全空間の pointed 射影そのもの。 -/
lemma unstraighteningVertexPrism_zero :
    prismEndpoint 0 _ ≫ unstraighteningVertexPrism F G x =
      pullback.fst pointedSpaceProjection F := by
  change simplexPrismVertex 1 0 (leftUnstraightening F) ≫ _ = _
  dsimp only [unstraighteningVertexPrism]
  rw [← Category.assoc, ← parameterVertex_naturality, Category.assoc,
    leftUnstraighteningTransformationFamilyLift_start, ← Category.assoc, lift_fst, Category.id_comp]

/-- 同じ制限の終点は、元の比較射の指定頂点における値そのもの。 -/
lemma unstraighteningVertexPrism_one :
    prismEndpoint 1 _ ≫ unstraighteningVertexPrism F G x =
      (leftUnstraighteningMappingVertexMap F G x).val ≫
        pullback.fst pointedSpaceProjection G := by
  rw [leftUnstraighteningMappingVertexMap_eq_family]
  have hp : leftUnstraighteningMappingFamily F G ≫ pullback.fst pointedSpaceProjection G =
      (simplexPrismVertex 1 1 (leftUnstraightening F) ▷
        leftUnstraighteningTransformationSpace F G) ≫
        leftUnstraighteningTransformationFamilyLift F G := pullback.lift_fst _ _ _
  change simplexPrismVertex 1 1 (leftUnstraightening F) ≫ _ = _
  dsimp only [unstraighteningVertexPrism]
  rw [← Category.assoc, ← parameterVertex_naturality, Category.assoc, Category.assoc, hp]

/-- 元の制限された持ち上げの底は、指定頂点の同じ元の全変換を厳密に保持する。 -/
lemma unstraighteningVertexPrism_projection :
    unstraighteningVertexPrism F G x ≫ pointedSpaceProjection =
      (Δ[1] ◁ leftUnstraighteningProjection F) ≫
        functorEdgePrism (intervalMappingEdgeOfVertex x) := by
  dsimp only [unstraighteningVertexPrism]
  rw [Category.assoc, leftUnstraighteningTransformationFamilyLift_projection,
    ← Category.assoc, parameterVertex_naturality, Category.assoc,
    unstraighteningTransformationFamily_at_vertex]

end SerrePositivity.InfinityCategories.F2.Compact
