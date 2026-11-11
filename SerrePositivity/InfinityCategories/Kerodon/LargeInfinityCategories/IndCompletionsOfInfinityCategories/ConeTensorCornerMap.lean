module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeTensorCorner

/-!
概要：一般の補間領域を、元の試験形状の射で制限する。
方針：元の二境界を pushout の普遍性で写し、元の積への包含と照合する。
規約：両全境界を保持し、試験形状の単射は同じ補間領域の単射へ移す。
使われ方：相対的な終点余錐の延長で元の旧族の全円柱を固定する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {A B : SSet.{u}} (f : A ⟶ B) (L : SSet.{u})
/-- 概要：元の試験形状の射を、同じ補間領域へ写す。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
def coneTensorCornerMap : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCorner A L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCorner B L :=
  pushout.desc
    ((f ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u})) ≫
      pushout.inl (B ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0] ▷ L))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ L) ≫
      pushout.inr (B ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0] ▷ L)) (by
      rw [← Category.assoc, whisker_exchange f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})),
        Category.assoc, pushout.condition]
      simp only [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap])
/-- 概要：元の試験族側の全制限を回収する。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
lemma coneTensorCornerMap_old :
    pushout.inl (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ L) ≫
      coneTensorCornerMap f L = (f ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u})) ≫
        pushout.inl (B ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0] ▷ L) :=
  pushout.inl_desc _ _ _
/-- 概要：下方余錐側の全制限を回収する。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
lemma coneTensorCornerMap_lower :
    pushout.inr (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ▷ L) ≫
      coneTensorCornerMap f L = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ L) ≫
        pushout.inr (B ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0] ▷ L) :=
  pushout.inr_desc _ _ _
/-- 概要：補間領域の射は元の積への包含と厳密に可換。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
lemma coneTensorCornerInclusion_naturality :
    coneTensorCornerMap f L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion B L =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion A L ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u})) := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, coneTensorCornerMap_old, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_old]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_old,
      ← comp_whiskerRight, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
  · simp only [← Category.assoc, coneTensorCornerMap_lower, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_lower]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorCornerInclusion_lower]
    exact (whisker_exchange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u}))).symm
/-- 概要：元の試験形状の単射は同じ補間領域の単射になる。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
instance coneTensorCornerMap_mono [Mono f] : Mono (coneTensorCornerMap f L) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u})) :=
    (tensorRight _).map_mono _
  exact mono_of_mono_fac (coneTensorCornerInclusion_naturality f L)
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
