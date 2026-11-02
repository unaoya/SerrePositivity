module

public import SerrePositivity.InfinityCategories.F2.Compact.UnstraighteningVertexPrism
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoconeIntervalTransportUnit
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoconeUnitFamilyEndpoints

/-!
概要：元の指定余錐の fiber 写像そのものを終点とする、同じ join 上の実際の prism。
方針：選択済み変換の持ち上げを元の余錐の単位頂点で評価し、全空間の射影を計算。
規約：元の coconeFiberMap を別の比較射へ置き換えず、両端と底を厳密に保つ。
使われ方：宇宙変更前後の同じ fiber 写像の全自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の余錐の全空間係数を付けた、元の join の同じ単位円柱。 -/
def coconeFiberBasePrism : (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ join B Δ[0] :=
  (Δ[1] ◁ leftUnstraighteningProjection F) ≫
    (β_ (Δ[1] : SSet.{u + 1}) B).hom ≫ coconeUnitCylinderMap B

/-- 同じ底の prism の始点は、元の全空間射影の後の図式部分の包含。 -/
lemma coconeFiberBasePrism_zero :
    prismEndpoint 0 _ ≫ coconeFiberBasePrism (F := F) =
      leftUnstraighteningProjection F ≫ joinInl B Δ[0] := by
  rw [coconeFiberBasePrism, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
    ← Category.assoc (prismEndpoint 0 B), prismEndpoint_zero_braiding,
    coconeUnitCylinderMap_zero]

/-- 同じ底の prism の終点は、元の指定頂点への右包含の定値族。 -/
lemma coconeFiberBasePrism_one :
    prismEndpoint 1 _ ≫ coconeFiberBasePrism (F := F) =
      SSet.const (SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u + 1}))) := by
  rw [coconeFiberBasePrism, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
    ← Category.assoc (prismEndpoint 1 B), prismEndpoint_one_braiding,
    coconeUnitCylinderMap_one, SSet.comp_const]

/-- 元の全余錐の指定単位頂点における、元の選択済み持ち上げ。 -/
def coconeFiberPrism (c : JoinCocone F) :
    (Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u} :=
  unstraighteningVertexPrism F (SSet.const c.vertex) (coconeTransformationVertex c)

/-- 元の prism の始点は、元の全空間の pointed 射影。 -/
lemma coconeFiberPrism_zero (c : JoinCocone F) :
    prismEndpoint 0 _ ≫ coconeFiberPrism c = pullback.fst pointedSpaceProjection F :=
  unstraighteningVertexPrism_zero _ _ _

/-- 元の prism の終点は、元の指定された fiber 写像自身の包含。 -/
lemma coconeFiberPrism_one (c : JoinCocone F) :
    prismEndpoint 1 _ ≫ coconeFiberPrism c =
      coconeFiberMap c ≫ vertexFiberι pointedSpaceProjection c.vertex := by
  rw [coconeFiberPrism, unstraighteningVertexPrism_one,
    coconeFiberMap_eq_unit_projection, Category.assoc, constantUnstraighteningFiberProjection_ι]

/-- 同じ元の prism は、元の join 円柱と元の全余錐の合成を厳密に被覆する。 -/
lemma coconeFiberPrism_projection (c : JoinCocone F) :
    coconeFiberPrism c ≫ pointedSpaceProjection = coconeFiberBasePrism (F := F) ≫ c.val := by
  rw [coconeFiberPrism, unstraighteningVertexPrism_projection]
  change (Δ[1] ◁ leftUnstraighteningProjection F) ≫
    ((β_ (Δ[1] : SSet.{u + 1}) B).hom ≫ (coconeTransformationHomotopy c).h) = _
  rw [coconeTransformationHomotopy_h]
  simp only [coconeFiberBasePrism, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Compact
