module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordMergeIndices
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordSurjectionComparison

/-!
# 元の二つの基本合成の短い語への共通余錐

概要：二つの隣接等色合成は、元の語の写像として短い共通終域への可換余錐を持つ。
方針：元の二重全射の合成則と全射からの終域の回収を使う。
規約：単体の図式や余極限の値を使わず、元の列の写像の等式を証明する。
使われ方：非交互の最大長の語を除く包含の Final 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma merge_cone_ordered {k : ℕ} (d : Fin (k + 3) → Direction)
    (i j : Fin (k + 1)) (hij : i ≤ j)
    (hi : d i.castSucc.castSucc = d i.castSucc.succ)
    (hj : d j.succ.castSucc = d j.succ.succ) :
    ∃ b : Word, b.length < k + 3 ∧
      ∃ l : mergeTarget d i.castSucc ⟶ b, ∃ r : mergeTarget d j.succ ⟶ b,
        mergeMap d i.castSucc hi ≫ l = mergeMap d j.succ hj ≫ r := by
  let f := mergeMap d i.castSucc hi
  let g := mergeMap d j.succ hj
  have hL := merge_left_remaining_color d i j hij hi hj
  have hR := merge_right_remaining_color d i j hij hi hj
  let f' := mergeMap (mergeTarget d i.castSucc).direction j hL
  let g' := mergeMap (mergeTarget d j.succ).direction i hR
  have hf : Function.Surjective (f ≫ f').orderHom :=
    (mergeMap_surjective (mergeTarget d i.castSucc).direction j hL).comp
      (mergeMap_surjective d i.castSucc hi)
  obtain ⟨hbc, he⟩ := target_eq_of_surjective (f ≫ f') (g ≫ g') hf rfl
    (fun x => merge_predAbove_comp i j hij x)
  refine ⟨_, Nat.lt_add_of_pos_right (by decide : 0 < 2), f' ≫ eqToHom hbc, g', ?_⟩
  exact (Category.assoc f f' (eqToHom hbc)).symm.trans he

lemma merge_cone_of_lt {k : ℕ} (d : Fin (k + 2) → Direction)
    (p q : Fin (k + 1)) (hpq : p < q)
    (hp : d p.castSucc = d p.succ) (hq : d q.castSucc = d q.succ) :
    ∃ b : Word, b.length < k + 2 ∧
      ∃ l : mergeTarget d p ⟶ b, ∃ r : mergeTarget d q ⟶ b,
        mergeMap d p hp ≫ l = mergeMap d q hq ≫ r := by
  cases k with
  | zero =>
    have hp' := p.isLt
    have hq' := q.isLt
    change p.val < q.val at hpq
    omega
  | succ k =>
    let i : Fin (k + 1) := ⟨p.val, by have := q.isLt; change p.val < q.val at hpq; omega⟩
    let j : Fin (k + 1) := q.pred (Fin.ne_zero_of_lt hpq)
    have hi : i.castSucc = p := by apply Fin.ext; rfl
    have hj : j.succ = q := Fin.succ_pred q _
    have hij : i ≤ j := by
      have he := congrArg Fin.val hj
      change j.val + 1 = q.val at he
      change p.val < q.val at hpq
      change i.val ≤ j.val
      dsimp only [i]
      omega
    clear_value i j
    subst p
    subst q
    exact merge_cone_ordered d i j hij hp hq

/-- 同じ位置も含む元の二つの基本合成を、短い語で可換に比較する。 -/
lemma merge_cone {k : ℕ} (d : Fin (k + 2) → Direction) (p q : Fin (k + 1))
    (hp : d p.castSucc = d p.succ) (hq : d q.castSucc = d q.succ) :
    ∃ b : Word, b.length < k + 2 ∧
      ∃ l : mergeTarget d p ⟶ b, ∃ r : mergeTarget d q ⟶ b,
        mergeMap d p hp ≫ l = mergeMap d q hq ≫ r := by
  rcases lt_trichotomy p q with h | h | h
  · exact merge_cone_of_lt d p q h hp hq
  · subst q
    exact ⟨_, Nat.lt_succ_self _, 𝟙 _, 𝟙 _, rfl⟩
  · obtain ⟨b, hb, l, r, he⟩ := merge_cone_of_lt d q p h hq hp
    exact ⟨b, hb, r, l, he.symm⟩

end SerrePositivity.EInfinity.Hammock.Word
