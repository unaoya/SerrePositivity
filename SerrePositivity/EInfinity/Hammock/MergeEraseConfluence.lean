module

public import SerrePositivity.EInfinity.Hammock.MergeEraseOverlap
public import SerrePositivity.EInfinity.Hammock.MergeEraseSquare

/-!
# 元の隣接合成と恒等列削除の局所合流

概要：任意の基本合成と基本削除は、各側0〜1段で同じ元の未縮約対象へ到達する。
方針：重なる場合は相殺、外側の場合は単体圏の面・退化の可換四角形を用いる。
規約：削除列が左側・右側の両方を含み、全次数で元の対象を比較する。
使われ方：基本縮約全体の局所合流。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {n : SimplexCategoryᵒᵖ}

/-- 元の基本合成と削除のすべての相対位置での局所合流。 -/
lemma merge_erase_join {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) (j : Fin (k + 2))
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n)
    (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n,
      Relation.ReflGen (Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ⟩ s ∧
      Relation.ReflGen (Reduction W X Y n)
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) j, eraseSimplex W X Y j τ hτ⟩ s := by
  by_cases hj : j = p.castSucc ∨ j = p.succ
  · refine ⟨_, Relation.ReflGen.refl, ?_⟩
    rw [merge_erase_overlap_eq W X Y d p hp j hj τ hτ]
  have hpos : j < p.castSucc ∨ p.succ < j := by
    have h0 : j.val ≠ p.val := fun h => hj (Or.inl (Fin.ext h))
    have h1 : j.val ≠ p.val + 1 := fun h => hj (Or.inr (Fin.ext h))
    change j.val < p.val ∨ p.val + 1 < j.val
    omega
  cases k with
  | zero =>
    have hp' := p.isLt
    have hj' := j.isLt
    rcases hpos with h | h
    · change j.val < p.val at h
      omega
    · change p.val + 1 < j.val at h
      omega
  | succ k =>
    rcases hpos with hlt | hgt
    · have hp0 : p ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        change p.val = 0 at hv
        have hvlt : j.val < p.val := hlt
        omega
      let q : Fin (k + 1) := p.pred hp0
      let i : Fin (k + 2) := ⟨j.val, by have := p.isLt; have : j.val < p.val := hlt; omega⟩
      have hq : q.succ = p := Fin.succ_pred p hp0
      have hi : i.castSucc = j := by apply Fin.ext; rfl
      have hle : i ≤ q.castSucc := by
        have hv := congrArg Fin.val hq
        change q.val + 1 = p.val at hv
        have hvlt : j.val < p.val := hlt
        change i.val ≤ q.val
        dsimp only [i]
        omega
      clear_value i q
      subst p
      subst j
      apply merge_erase_join_of_square W X Y d q.succ hp i.castSucc q i ?_ τ hτ
      intro x
      exact congrArg
        (fun f : SimplexCategory.mk (k + 1) ⟶ SimplexCategory.mk (k + 1) => f.toOrderHom x)
        (SimplexCategory.δ_comp_σ_of_le hle)
    · have hj0 : j ≠ 0 := by
        intro h
        have hv := congrArg Fin.val h
        change j.val = 0 at hv
        have hvlt : p.val + 1 < j.val := hgt
        omega
      let q : Fin (k + 1) := ⟨p.val, by
        have := j.isLt
        have : p.val + 1 < j.val := hgt
        omega⟩
      let i : Fin (k + 2) := j.pred hj0
      have hq : q.castSucc = p := by apply Fin.ext; rfl
      have hi : i.succ = j := Fin.succ_pred j hj0
      have hlt : q.castSucc < i := by
        have hv := congrArg Fin.val hi
        change i.val + 1 = j.val at hv
        have hvlt : p.val + 1 < j.val := hgt
        change q.val < i.val
        dsimp only [q]
        omega
      clear_value i q
      subst p
      subst j
      apply merge_erase_join_of_square W X Y d q.castSucc hp i.succ q i ?_ τ hτ
      intro x
      exact congrArg
        (fun f : SimplexCategory.mk (k + 1) ⟶ SimplexCategory.mk (k + 1) => f.toOrderHom x)
        (SimplexCategory.δ_comp_σ_of_gt hlt)

end SerrePositivity.EInfinity.Hammock
