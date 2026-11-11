module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ArrowInterpolationCorner

/-!
概要：元の補間領域を、試験形状の任意の制限で写す。
方針：同じ始点の全族上の pushout の普遍性を使う。
規約：円柱と始点余錐の両脚を保持。使われ方：補間族の元の試験族への制限。

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
variable {A B : SSet.{u}} (f : A ⟶ B)

/-- 同じ全円柱と始点全余錐の制限から作る、実補間領域の射。 -/
def arrowInterpolationCornerMap : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCorner B :=
  pushout.desc ((f ▷ (Δ[1] : SSet.{u})) ≫ pushout.inl (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0]))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) ≫ pushout.inr (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0])) (by
      rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, pushout.condition,
        ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc])

/-- 実補間領域の制限は、元の全円柱の制限を保持する。 -/
lemma arrowInterpolationCornerMap_old : pushout.inl (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ≫
    arrowInterpolationCornerMap f = (f ▷ (Δ[1] : SSet.{u})) ≫
      pushout.inl (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0]) := pushout.inl_desc _ _ _

/-- 同じ制限は、始点の元の全余錐の制限も保持する。 -/
lemma arrowInterpolationCornerMap_source : pushout.inr (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ≫
    arrowInterpolationCornerMap f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) ≫
      pushout.inr (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0]) := pushout.inr_desc _ _ _

/-- 実補間領域の射は、元の全円柱への包含と厳密に可換。 -/
lemma arrowInterpolationCornerInclusion_naturality :
    arrowInterpolationCornerMap f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion A ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) ▷ (Δ[1] : SSet.{u})) := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, arrowInterpolationCornerMap_old,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion_old]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion_old,
      ← MonoidalCategory.comp_whiskerRight, ← MonoidalCategory.comp_whiskerRight,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
  · simp only [← Category.assoc, arrowInterpolationCornerMap_source,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion_source]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.arrowInterpolationCornerInclusion_source, SSet.ι₀_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
