module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedConeNormalizeNext

/-! # 標準退化錐の全正番号面

概要：退化表示で選ぶ標準錐の全正番号面が、同じ下次数錐の指定面に一致する。
方針：二つの恒等面と、その前後の面を単体恒等式で計算する。
規約：零次元も直接検証する。使われ方：次次数の退化正規化の全面保存。
-/
@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
universe u
variable {K X : SSet.{u}} {f : K ⟶ X}
/-- 退化位置より前の正番号面。 -/
lemma truncatedConeDegeneracy_face_lower {n : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f (n + 1))
    (i : Fin (n + 1)) (k : Fin (n + 2)) (hk : k ≤ i.castSucc) (y : K _⦋n + 1⦌) :
    X.δ k.castSucc.succ (X.σ i.succ.succ (C.simplex (n + 1) le_rfl y)) =
      C.simplex (n + 1) le_rfl (K.δ k.castSucc (K.σ i.succ y)) := by
  have hx := X.δ_comp_σ_of_le_apply (i := k.succ) (j := i.succ)
    (by simpa only [Fin.castSucc_succ, Fin.succ_le_succ_iff] using hk)
    (C.simplex (n + 1) le_rfl y)
  rw [Fin.castSucc_succ, C.face_positive n le_rfl y k] at hx
  rw [K.δ_comp_σ_of_le_apply hk y, ← C.degeneracy_positive n le_rfl _ i]
  exact hx
/-- 退化位置より後の正番号面。 -/
lemma truncatedConeDegeneracy_face_upper {n : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f (n + 1))
    (i : Fin (n + 1)) (k : Fin (n + 2)) (hk : i.castSucc < k) (y : K _⦋n + 1⦌) :
    X.δ k.succ.succ (X.σ i.castSucc.succ (C.simplex (n + 1) le_rfl y)) =
      C.simplex (n + 1) le_rfl (K.δ k.succ (K.σ i.castSucc y)) := by
  have hx := X.δ_comp_σ_of_gt_apply (i := k.succ) (j := i.succ)
    (by simpa only [Fin.castSucc_succ, Fin.succ_lt_succ_iff] using hk)
    (C.simplex (n + 1) le_rfl y)
  rw [Fin.castSucc_succ, C.face_positive n le_rfl y k] at hx
  rw [K.δ_comp_σ_of_gt_apply hk y, ← C.degeneracy_positive n le_rfl _ i]
  exact hx
/-- 標準退化錐の全正番号面は同じ下次数錐の指定値。 -/
lemma truncatedConeDegeneracy_face_positive {N : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    (i : Fin (N + 1)) (k : Fin (N + 2)) (y : K _⦋N⦌) :
    X.δ k.succ (X.σ i.succ (C.simplex N le_rfl y)) =
      C.simplex N le_rfl (K.δ k (K.σ i y)) := by
  cases N with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; have h := i.isLt; change i.val = 0; omega
    subst i
    fin_cases k
    · change X.δ (1 : Fin 2).castSucc (X.σ (1 : Fin 2) _) =
        C.simplex 0 le_rfl (K.δ (0 : Fin 1).castSucc (K.σ (0 : Fin 1) y))
      rw [X.δ_comp_σ_self_apply, K.δ_comp_σ_self_apply]
    · change X.δ (1 : Fin 2).succ (X.σ (1 : Fin 2) _) =
        C.simplex 0 le_rfl (K.δ (0 : Fin 1).succ (K.σ (0 : Fin 1) y))
      rw [X.δ_comp_σ_succ_apply, K.δ_comp_σ_succ_apply]
  | succ n =>
    by_cases hself : k = i.castSucc
    · subst k
      simp only [← Fin.castSucc_succ, X.δ_comp_σ_self_apply, K.δ_comp_σ_self_apply]
    by_cases hsucc : k = i.succ
    · subst k
      simp only [X.δ_comp_σ_succ_apply, K.δ_comp_σ_succ_apply]
    rcases lt_or_gt_of_ne hself with hlo | hhi
    · have hi : i ≠ 0 := by
        intro he
        have hv : k.val < i.val := hlo
        rw [he] at hv
        simp at hv
      have hk : k ≠ Fin.last (n + 2) := by
        intro he
        have hv : k.val < i.val := hlo
        rw [he, Fin.val_last] at hv
        omega
      have hle : k.castPred hk ≤ (i.pred hi).castSucc := by
        change k.val ≤ i.val - 1
        have hv : k.val < i.val := hlo
        omega
      have he := truncatedConeDegeneracy_face_lower C (i.pred hi) (k.castPred hk) hle y
      simpa only [Fin.succ_pred, Fin.castSucc_castPred] using he
    · have hv : i.val + 1 < k.val := by
        have hv : i.val < k.val := hhi
        have hn : k.val ≠ i.val + 1 := by
          intro he
          exact hsucc (Fin.ext he)
        omega
      have hi : i ≠ Fin.last (n + 1) := by
        intro he
        rw [he, Fin.val_last] at hv
        omega
      have hk : k ≠ 0 := by
        intro he
        rw [he] at hv
        simp at hv
      have hlt : (i.castPred hi).castSucc < k.pred hk := by
        change i.val < k.val - 1
        omega
      have he := truncatedConeDegeneracy_face_upper C (i.castPred hi) (k.pred hk) hlt y
      simpa only [Fin.succ_pred, Fin.castSucc_castPred] using he
/-- 正規化は指定した全正番号面を保つ。 -/
lemma truncatedConeNormalizeNext_face_positive {N : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)
    (U : K _⦋N + 1⦌ → X _⦋N + 2⦌)
    (hU : ∀ σ k, X.δ k.succ (U σ) = C.simplex N le_rfl (K.δ k σ))
    (σ : K _⦋N + 1⦌) (k : Fin (N + 2)) :
    X.δ k.succ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNormalizeNext C U σ) = C.simplex N le_rfl (K.δ k σ) := by
  classical
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNormalizeNext
  split_ifs with h
  · exact (truncatedConeDegeneracy_face_positive C h.choose k h.choose_spec.choose).trans
      (congrArg (fun w => C.simplex N le_rfl (K.δ k w)) h.choose_spec.choose_spec.symm)
  · exact hU σ k
end SerrePositivity.InfinityCategories.Project.DerivedCategories
