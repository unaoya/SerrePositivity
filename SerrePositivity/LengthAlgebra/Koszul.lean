module

public import SerrePositivity.PerfectComplex.ProjectiveBounds
public import SerrePositivity.LengthAlgebra.SerreQuotient

/-! # 長さ付き代数の Koszul 有限性と Euler 特性

有限性と正の homological 次数の消滅を独立な条件として扱う。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)
  {e : ℕ} (z : Fin e → C)

/-- 全ての正の冪について、各次数の Koszul ホモロジーの長さが有限。 -/
def KoszulFinite : Prop :=
  ∀ v : ℕ, 0 < v → ∀ q : ℤ, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤

/-- 全ての正の冪について、正の homological 次数の Koszul ホモロジーが長さ零。 -/
def KoszulAcyclic : Prop :=
  ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology (-(i : ℤ))) = 0

/-- Koszul Euler 特性。Koszul 有限性の下で長さの有限交代和となる。 -/
noncomputable def koszulEuler : ℝ := lambdaEuler lam (koszulComplex z)

/-- 台をもつ有界有限射影複体のホモロジーは、有限な長さの評価先に属する。 -/
theorem homology_mem_finiteLengthTorsion (hfg : J.FG)
    (hJ : J ≤ (Ideal.span (Set.range z)).radical) (hfin : KoszulFinite lam z)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfinite : ∀ q, Module.Finite C (P.X q))
    (hproj : ∀ q, Module.Projective C (P.X q))
    (hbound : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (hsupp : IsSupported z P) (q : ℤ) : finiteLengthTorsion lam (P.homology q) :=
  ⟨supported_homology_isPowTorsion hfg hJ hsupp q,
    lambdaHomology_supported_projective_ne_top lam hfg z hJ hfin P hfinite hproj hbound hsupp q⟩

/-- 非負の homological 次数での有限性から、全 cochain 次数での有限性を得る。 -/
lemma koszul_finite_of_homologySelf
    (hfin : ∀ i : ℕ, lam.len (koszulHomologySelf z i) ≠ ⊤) (q : ℤ) :
    lam.len ((koszulComplex z).homology q) ≠ ⊤ := by
  by_cases hq : 0 < q
  · have := ModuleCat.subsingleton_of_isZero (koszulComplex_isZero_homology_of_pos z q hq)
    rw [lam.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, q = -(i : ℤ) := ⟨(-q).toNat, by omega⟩
    exact hfin i

/-- 正の Koszul ホモロジーが長さ零なら、Koszul Euler 数は第零商の長さ。 -/
lemma koszulEuler_eq_length_quotient
    (hz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf z i) = 0) :
    koszulEuler lam z = (lam.len (C ⧸ Ideal.span (Set.range z))).toReal := by
  unfold koszulEuler lambdaEuler
  rw [finsum_eq_single _ (0 : ℤ)]
  · rw [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul,
      lam.len_congr _ _ (koszulComplex_homology_zero_equiv z).some]
  · intro q hq
    rcases lt_or_gt_of_ne hq with hq | hq
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, q = -(i : ℤ) := ⟨(-q).toNat, by omega⟩
      have h := hz i (by omega)
      change lam.len ((koszulComplex z).homology (-(i : ℤ))) = 0 at h
      simp [h]
    · have := ModuleCat.subsingleton_of_isZero (koszulComplex_isZero_homology_of_pos z q hq)
      simp [lam.len_eq_zero_of_subsingleton]

end SerrePositivity.LengthAlgebra
