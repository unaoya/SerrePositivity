module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyConeRealization

/-!
概要：錐の実現が保持する両端固定比較を左右の端へ制限する。
方針：全境界の式へ二つの包含を前合成する。
規約：全比較時間で同じ頂点と図式を保つ。
使われ方：実現した錐と指定変換の円柱の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
  {H : SSet.Homotopy (SSet.const z) f}

/-- 実現の比較の左端は、全時刻で同じ指定頂点。 -/
lemma homotopyConeRealization_left (R : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyConeRealization H) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h = SSet.const z := by
  have h := congrArg (fun q ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl Δ[0] K ▷ (Δ[1] : SSet.{u})) ≫ q)
    R.boundary
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_fatInclusion,
    ← Category.assoc, whiskerRight_fst, Category.assoc] at h
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h =
    fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm z at h
  rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const] at h
  exact h

/-- 実現の比較の右端は、全時刻で同じ元の図式。 -/
lemma homotopyConeRealization_right (R : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HomotopyConeRealization H) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h = fst K Δ[1] ≫ f := by
  have h := congrArg (fun q ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr Δ[0] K ▷ (Δ[1] : SSet.{u})) ≫ q)
    R.boundary
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_fatInclusion,
    ← Category.assoc, whiskerRight_fst, Category.assoc] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
