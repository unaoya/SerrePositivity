module
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullJoinIso
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.F2.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

def excisionReplaceInitial {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F)) :
    nerve ExcisionGridIndex.{u} ⟶ X :=
  excisionFullJoinIso.inv ≫ c.val

lemma excisionReplaceInitial_restrict {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F)) :
    nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ excisionReplaceInitial c =
      nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F := by
  rw [← excisionFullJoinIso_inr]
  change (joinInr Δ[0] (nerve ExcisionFullPuncturedIndex) ≫ excisionFullJoinIso.hom) ≫
    (excisionFullJoinIso.inv ≫ c.val) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact c.property

lemma excisionReplaceInitial_vertex {X : SSet.{u}}
    {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F)) :
    (excisionReplaceInitial c).app (Opposite.op ⦋0⦌)
      (nerveVertex excisionGridInitialPoint) = c.vertex := by
  rw [JoinCone.vertex_eq]
  have h := congrArg (fun q ↦ q ≫ excisionFullJoinIso.{u}.inv) excisionFullJoinIso_inl
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  rw [h, Category.assoc, SSet.yonedaEquiv_comp]
  rfl

end SerrePositivity.InfinityCategories
