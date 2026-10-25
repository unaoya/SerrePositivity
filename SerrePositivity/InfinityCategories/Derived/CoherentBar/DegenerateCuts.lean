module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateFaces
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBar_prefix_degenerate {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ n + 1) (hj : j.val + 1 ≤ k) :
    (dgCoherentBarPrefix (I.σ j s) k hk).2 ∈ I.degenerate k := by
  let α := SimplexCategory.mkHom (dgCoherentBarPrefixOrder (n + 1) k hk) ≫
    SimplexCategory.σ j
  have hα : ¬Function.Injective α.toOrderHom := by
    intro hi
    let a : Fin (k + 1) := ⟨j.val, by omega⟩
    let b : Fin (k + 1) := ⟨j.val + 1, by omega⟩
    have ha : dgCoherentBarPrefixOrder (n + 1) k hk a = j.castSucc := Fin.ext rfl
    have hb : dgCoherentBarPrefixOrder (n + 1) k hk b = j.succ := Fin.ext rfl
    have hab : a = b := hi (by
      change j.predAbove (dgCoherentBarPrefixOrder (n + 1) k hk a) =
        j.predAbove (dgCoherentBarPrefixOrder (n + 1) k hk b)
      rw [ha, hb]
      simp)
    have h := congrArg Fin.val hab
    dsimp [a, b] at h
    omega
  have h := dgCoherentBar_map_degenerate_of_not_injective s α hα
  simpa only [α, op_comp, CategoryTheory.Functor.map_comp, types_comp_apply,
    dgCoherentBarPrefix, SimplicialObject.σ] using h

lemma dgCoherentBar_tail_degenerate {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (k : ℕ) (hk : k ≤ n + 1) (hj : k ≤ j.val) :
    (dgCoherentBarTail (I.σ j s) k hk).2 ∈ I.degenerate (n + 1 - k) := by
  let α := SimplexCategory.mkHom (dgCoherentBarTailOrder (n + 1) k hk) ≫
    SimplexCategory.σ j
  have hα : ¬Function.Injective α.toOrderHom := by
    intro hi
    let a : Fin (n + 1 - k + 1) := ⟨j.val - k, by omega⟩
    let b : Fin (n + 1 - k + 1) := ⟨j.val - k + 1, by omega⟩
    have ha : dgCoherentBarTailOrder (n + 1) k hk a = j.castSucc := by
      apply Fin.ext
      dsimp [dgCoherentBarTailOrder, a]
      omega
    have hb : dgCoherentBarTailOrder (n + 1) k hk b = j.succ := by
      apply Fin.ext
      dsimp [dgCoherentBarTailOrder, b]
      omega
    have hab : a = b := hi (by
      change j.predAbove (dgCoherentBarTailOrder (n + 1) k hk a) =
        j.predAbove (dgCoherentBarTailOrder (n + 1) k hk b)
      rw [ha, hb]
      simp)
    have h := congrArg Fin.val hab
    dsimp [a, b] at h
    omega
  have h := dgCoherentBar_map_degenerate_of_not_injective s α hα
  simpa only [α, op_comp, CategoryTheory.Functor.map_comp, types_comp_apply,
    dgCoherentBarTail, SimplicialObject.σ] using h

end SerrePositivity.InfinityCategories
