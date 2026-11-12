module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaces
/-!
概要：退化位置が切断の左右どちらに残るかを元の prefix・tail ラベルで判定する。
方針：重複二頂点を明示し、Mathlib の非退化単体の単射性判定に帰着する。
規約：次数と切断位置を保持し、coherent 係数を通常の辺の合成で置換しない。
使われ方：実 theta の prefix 項が退化部分を保存することの検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBar_prefix_degenerate {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ n + 1) (hj : j.val + 1 ≤ k) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix (I.σ j s) k hk).2 ∈ I.degenerate k := by
  let α := SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) k hk) ≫
    SimplexCategory.σ j
  have hα : ¬Function.Injective α.toOrderHom := by
    intro hi
    let a : Fin (k + 1) := ⟨j.val, by omega⟩
    let b : Fin (k + 1) := ⟨j.val + 1, by omega⟩
    have ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) k hk a = j.castSucc := Fin.ext rfl
    have hb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) k hk b = j.succ := Fin.ext rfl
    have hab : a = b := hi (by
      change j.predAbove (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) k hk a) =
        j.predAbove (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixOrder (n + 1) k hk b)
      rw [ha, hb]
      simp)
    have h := congrArg Fin.val hab
    dsimp [a, b] at h
    omega
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_map_degenerate_of_not_injective s α hα
  simpa only [α, op_comp, CategoryTheory.Functor.map_comp, types_comp_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix, SimplicialObject.σ] using h

lemma dgCoherentBar_tail_degenerate {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ n + 1) (hj : k ≤ j.val) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail (I.σ j s) k hk).2 ∈ I.degenerate (n + 1 - k) := by
  let α := SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) k hk) ≫
    SimplexCategory.σ j
  have hα : ¬Function.Injective α.toOrderHom := by
    intro hi
    let a : Fin (n + 1 - k + 1) := ⟨j.val - k, by omega⟩
    let b : Fin (n + 1 - k + 1) := ⟨j.val - k + 1, by omega⟩
    have ha : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) k hk a = j.castSucc := by
      apply Fin.ext
      dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder, a]
      omega
    have hb : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) k hk b = j.succ := by
      apply Fin.ext
      dsimp [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder, b]
      omega
    have hab : a = b := hi (by
      change j.predAbove (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) k hk a) =
        j.predAbove (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTailOrder (n + 1) k hk b)
      rw [ha, hb]
      simp)
    have h := congrArg Fin.val hab
    dsimp [a, b] at h
    omega
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_map_degenerate_of_not_injective s α hα
  simpa only [α, op_comp, CategoryTheory.Functor.map_comp, types_comp_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail, SimplicialObject.σ] using h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
