module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedGraded
/-!
概要：退化単体の二つの例外面以外は、元の単体的集合でも退化している。
方針：Mathlib の非退化単体の単射性判定を使い、残る重複二頂点で非単射性を示す。
規約：元のラベルを保持する。例外二面の符号相殺は係数側で別に照合する。
使われ方：同じ theta が退化部分を保存することの面項の検証。
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

lemma dgCoherentBar_map_degenerate_of_not_injective {n m : ℕ}
    (s : I _⦋m⦌) (α : ⦋n⦌ ⟶ ⦋m⦌) (hα : ¬Function.Injective α.toOrderHom) :
    I.map α.op s ∈ I.degenerate n := by
  by_contra hs
  have hn : I.map α.op s ∈ I.nonDegenerate n := hs
  exact hα ((SimplexCategory.mono_iff_injective (f := α)).mp
    (I.mono_of_nonDegenerate ⟨_, hn⟩ α s rfl))

lemma dgCoherentBar_face_degenerate {n : ℕ} (s : I _⦋n⦌)
    (j : Fin (n + 1)) (i : Fin (n + 2))
    (h₁ : i ≠ j.castSucc) (h₂ : i ≠ j.succ) :
    I.δ i (I.σ j s) ∈ I.degenerate n := by
  by_contra hs
  have hn : I.δ i (I.σ j s) ∈ I.nonDegenerate n := hs
  let f := SimplexCategory.δ i ≫ SimplexCategory.σ j
  have hrepr : I.map f.op s = I.δ i (I.σ j s) := by
    simp only [f, op_comp, CategoryTheory.Functor.map_comp, types_comp_apply]
    rfl
  have hm := I.mono_of_nonDegenerate ⟨_, hn⟩ f s hrepr
  have hi := (SimplexCategory.mono_iff_injective (f := f)).mp hm
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h₁.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq h₂.symm
  have hab : a = b := hi (by
    change j.predAbove (i.succAbove a) = j.predAbove (i.succAbove b)
    rw [ha, hb]
    simp)
  have h := congrArg i.succAbove hab
  rw [ha, hb] at h
  exact (ne_of_lt j.castSucc_lt_succ) h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
