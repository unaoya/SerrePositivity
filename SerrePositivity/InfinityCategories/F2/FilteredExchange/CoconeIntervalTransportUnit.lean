module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeIntervalTransportSource
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantTargetVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantPullbackCoordinates
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTransportCoordinates

/-!
概要：元の余錐の輸送始域の二座標を、元の単位作用そのものへ厳密に戻す。
方針：元の fiber 写像の頂点を同じ単位作用の fiber 射影として計算する。
規約：余錐・単位・実射を保持。使われ方：下側輸送因子と元の三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F)
local notation "u₀" => leftUnstraighteningMappingVertexMap F (SSet.const c.vertex)
  (coconeTransformationVertex c)

/-- 元の余錐 fiber 写像は、同じ元の単位作用の fiber 射影に等しい。 -/
lemma coconeFiberMap_eq_unit_projection :
    coconeFiberMap c = Subtype.val u₀ ≫ constantUnstraighteningFiberProjection B c.vertex := by
  apply (functorVertexEquiv _ _).injective
  change functorVertex (coconeFiberMap c) = functorVertex _
  rw [coconeFiberMap_vertex]
  have h := constantUnstraighteningRelativeIso_vertex (leftUnstraighteningProjection F)
    c.vertex (Subtype.val u₀) (Subtype.property u₀)
  rw [leftUnstraighteningMappingVertexMap_vertex] at h
  exact h

/-- 元の二座標の輸送始域射は、元の単位作用に全係数の恒等射を添えた射そのもの。 -/
lemma coconeIntervalTransportSource_eq_unit_tensor (T : SSet.{u + 1}) :
    coconeIntervalTransportSource c T = Subtype.val u₀ ▷ T := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [whiskerRight_fst]
    dsimp only [coconeIntervalTransportSource]
    rw [lift_fst]
    apply pullback.hom_ext
    · rw [Category.assoc, constantPullbackFiberIso_inv_fst, ← Category.assoc, lift_fst]
      rw [coconeFiberMap_eq_unit_projection]
      simp only [Category.assoc, constantUnstraighteningFiberProjection_ι]
    · rw [Category.assoc, constantPullbackFiberIso_inv_snd, lift_snd]
      exact ((Category.assoc _ _ _).trans
        (congrArg (fun h => fst (leftUnstraightening F) T ≫ h) (Subtype.property u₀))).symm
  · rw [whiskerRight_snd]
    dsimp only [coconeIntervalTransportSource]
    rw [lift_snd]

/-- 元の係数での始域制限は、同じ単位作用の後に同じ係数を添える射に等しい。 -/
lemma coconeIntervalTransportSource_point {T : SSet.{u + 1}} (l : T _⦋0⦌) :
    lift (𝟙 (leftUnstraightening F)) (SSet.const l) ≫ coconeIntervalTransportSource c T =
      Subtype.val u₀ ≫ lift (𝟙 _) (SSet.const l) := by
  rw [coconeIntervalTransportSource_eq_unit_tensor]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst, Category.id_comp]
    rw [Category.assoc, lift_fst, Category.comp_id]
  · simp only [Category.assoc, whiskerRight_snd, lift_snd, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
