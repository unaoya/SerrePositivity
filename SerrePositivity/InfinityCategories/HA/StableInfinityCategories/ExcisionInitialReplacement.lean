module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridInitialPoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackConeVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveMonomorphism

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionReplaceInitial {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F)) :
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullJoinIso.inv ≫ c.val

lemma excisionReplaceInitial_restrict {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ excisionReplaceInitial c =
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullJoinIso_inr]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullJoinIso.hom) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullJoinIso.inv ≫ c.val) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact c.property

lemma excisionReplaceInitial_vertex {X : SSet.{u}}
    {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F)) :
    (excisionReplaceInitial c).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridInitialPoint) = c.vertex := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  have h := congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullJoinIso.{u}.inv) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullJoinIso_inl
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  rw [h, Category.assoc, SSet.yonedaEquiv_comp]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
