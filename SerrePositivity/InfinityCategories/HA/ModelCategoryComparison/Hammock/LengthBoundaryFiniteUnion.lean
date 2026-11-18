module

public import Mathlib.Data.Fintype.Powerset
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundary
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperSubsetImages

/-!
# 元の長さ境界の列部分集合による有限和表示

概要：短い語の全包含の像の和を、長さ以下の列部分集合の有限和として表示する。
方針：単射の像の語との比較と、その像の濃度を使う。
規約：等式は元の対象内の部分複体の等式である。
使われ方：proper 図式の元の境界への有限和の貼り合わせの適用。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

def boundarySubsets (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Finset (Finset (Fin c.length)) :=
  Finset.univ.filter (fun s => s.card ≤ n)

lemma mem_boundarySubsets (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (s : Finset (Fin c.length)) :
    s ∈ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.boundarySubsets n c ↔ s.card ≤ n := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.boundarySubsets, Finset.mem_filter, Finset.mem_univ, true_and]

lemma lengthBoundary_eq_finsetSup (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n c = (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.boundarySubsets n c).sup (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c) := by
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    apply iSup_le
    intro f
    apply iSup_le
    intro hf
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.range_eq_subsetImage F c f hf]
    apply Finset.le_sup
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.mem_boundarySubsets, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage_card_of_injective f hf]
    exact ha
  · apply Finset.sup_le
    intro s hs
    have hb : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword c s).length ≤ n := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.mem_boundarySubsets n c s).1 hs
    exact le_iSup_of_le (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword c s) (le_iSup_of_le hb
      (le_iSup_of_le (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s)
        (le_iSup_of_le (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective c s) le_rfl)))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
