module

public import SerrePositivity.EInfinity.CosimplicialNormalization.Components

/-!
# 全codegeneracyの核を交代余面微分が保つ

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L19、報告 §395。
同じcosimplicial恒等式で二つの隣接恒等項以外を消し、整数符号で相殺する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.CosimplicialNormalization
open CategoryTheory
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 隣接二項以外は元の入力のcodegeneracyの零へ戻る（Dold–Kan、BF §2.2）。 -/
lemma coface_codegeneracy_zero_of_not_neighbors {q : ℕ}
    (a : X.obj ⦋q⦌) (ha : a ∈ normalizedSubmodule A X q) (i : Fin (q + 1)) (j : Fin (q + 2))
    (h₀ : j ≠ i.castSucc) (h₁ : j ≠ i.succ) : (X.σ i) ((X.δ j) a) = 0 := by
  cases q with
  | zero =>
    exfalso
    have hn₀ : j.val ≠ i.val := fun h => h₀ (Fin.ext h)
    have hn₁ : j.val ≠ i.val + 1 := fun h => h₁ (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    omega
  | succ q =>
    have hσ := (mem_normalized_succ A X q a).mp ha
    by_cases hlt : j.val < i.val
    · have hi : i ≠ 0 := by intro h; subst i; simp at hlt
      let i' : Fin (q + 1) := i.pred hi
      let j' : Fin (q + 2) := j.castLT (by have hj := i.isLt; omega)
      have hjs : j'.castSucc = j := Fin.ext rfl
      have his : i'.succ = i := Fin.succ_pred i hi
      have hle : j' ≤ i'.castSucc := by
        change j.val ≤ (i.pred hi).val
        rw [Fin.val_pred]
        omega
      have H := ConcreteCategory.congr_hom (X.δ_comp_σ_of_le hle) a
      change (X.σ i'.succ) ((X.δ j'.castSucc) a) = (X.δ j') ((X.σ i') a) at H
      rw [hjs, his, hσ i', map_zero] at H
      exact H
    · have hgt : i.succ < j := by
        have hn₀ : j.val ≠ i.val := fun h => h₀ (Fin.ext h)
        have hn₁ : j.val ≠ i.val + 1 := fun h => h₁ (Fin.ext h)
        change i.val + 1 < j.val
        omega
      have hib : i.val < q + 1 := by
        have hij : i.val + 1 < j.val := hgt
        have hj := j.isLt
        omega
      have H := ConcreteCategory.congr_hom (X.δ_comp_σ_of_gt' hgt) a
      change (X.σ i) ((X.δ j) a) =
        (X.δ (j.pred hgt.ne_zero)) ((X.σ (i.castLT hib)) a) at H
      rw [hσ _, map_zero] at H
      exact H

/-- L19：元の正規化部分を元の交代余面微分が保つ（Dold–Kan、BF §2.2）。 -/
lemma normalized_d_mem_exact (q : ℕ) (a : normalizedSubmodule A X q) :
    ∀ i : Fin (q + 1), (X.σ i) (alternatingCofaces A X q a.val) = 0 := by
  intro i
  simp only [alternatingCofaces, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  have hn : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  rw [Finset.sum_eq_add_of_mem i.castSucc i.succ (Finset.mem_univ _) (Finset.mem_univ _) hn]
  · have h₀ := ConcreteCategory.congr_hom (X.δ_comp_σ_self (i := i)) a.val
    have h₁ := ConcreteCategory.congr_hom (X.δ_comp_σ_succ (i := i)) a.val
    change (X.σ i) ((X.δ i.castSucc) a.val) = a.val at h₀
    change (X.σ i) ((X.δ i.succ) a.val) = a.val at h₁
    rw [h₀, h₁]
    simp only [Fin.val_castSucc, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul]
    exact add_neg_cancel _
  · intro j _ hj
    rw [coface_codegeneracy_zero_of_not_neighbors A X a.val a.property i j hj.1 hj.2, smul_zero]

/-- 同じ正規化部分加群への微分の値（Dold–Kan、BF §2.2）。 -/
lemma alternatingCofaces_mem (q : ℕ) (a : normalizedSubmodule A X q) :
    alternatingCofaces A X q a.val ∈ normalizedSubmodule A X (q + 1) :=
  (mem_normalized_succ A X q _).mpr (normalized_d_mem_exact A X q a)

end SerrePositivity.EInfinity.CosimplicialNormalization
