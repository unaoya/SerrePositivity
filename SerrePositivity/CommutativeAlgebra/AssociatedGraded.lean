module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic
public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.DirectSum.Module

/-! # I 進随伴次数加群

`I^n M / I^(n+1) M` を実際の部分加群の商として定義する。
各次数は `I` で消え、準素イデアルの場合は有限長となる。
Samuel 関数を各次数の長さの部分和として表す。
-/

@[expose] public section

universe u

namespace SerrePositivity.HilbertSamuel

open IsLocalRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- I 進フィルトレーションの第 n 段。 -/
def adicSubmodule (n : ℕ) : Submodule R M := I ^ n • ⊤

lemma adicSubmodule_succ_le (n : ℕ) :
    adicSubmodule R I M (n + 1) ≤ adicSubmodule R I M n :=
  Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl

/-- `I^(n+1)M` を `I^nM` 内の部分加群として見たもの。 -/
def gradedDenominator (n : ℕ) : Submodule R (adicSubmodule R I M n) :=
  (adicSubmodule R I M (n + 1)).comap (adicSubmodule R I M n).subtype

/-- 随伴次数加群の第 n 次成分 `I^nM / I^(n+1)M`。 -/
abbrev GradedPiece (n : ℕ) := adicSubmodule R I M n ⧸ gradedDenominator R I M n

lemma smul_mem_adicSubmodule (a : I) {n : ℕ} {x : M}
    (hx : x ∈ adicSubmodule R I M n) :
    (a : R) • x ∈ adicSubmodule R I M (n + 1) := by
  change (a : R) • x ∈ I ^ (n + 1) • (⊤ : Submodule R M)
  rw [pow_succ', mul_smul]
  exact Submodule.smul_mem_smul a.2 hx

/-- I の元の乗法は、I 進部分加群の次数を一つ上げる。 -/
def adicMultiplication (a : I) (n : ℕ) :
    adicSubmodule R I M n →ₗ[R] adicSubmodule R I M (n + 1) where
  toFun x := ⟨(a : R) • (x : M), smul_mem_adicSubmodule R I M a x.2⟩
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' r x := Subtype.ext (smul_comm (a : R) r (x : M))

/-- 次数一の元の乗法を、随伴次数加群の各商へ降ろす。 -/
def gradedMultiplication (a : I) (n : ℕ) :
    GradedPiece R I M n →ₗ[R] GradedPiece R I M (n + 1) :=
  (gradedDenominator R I M n).mapQ (gradedDenominator R I M (n + 1))
    (adicMultiplication R I M a n) (by
      intro x hx
      exact smul_mem_adicSubmodule R I M a hx)

@[simp]
lemma gradedMultiplication_mk (a : I) (n : ℕ) (x : adicSubmodule R I M n) :
    gradedMultiplication R I M a n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (adicMultiplication R I M a n x) := rfl

/-- 第 n 次成分の長さ。 -/
noncomputable def hilbertFunction (n : ℕ) : ℕ∞ := Module.length R (GradedPiece R I M n)

lemma ideal_le_annihilator_gradedPiece (n : ℕ) :
    I ≤ Module.annihilator R (GradedPiece R I M n) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change a • (x : M) ∈ I ^ (n + 1) • (⊤ : Submodule R M)
  rw [pow_succ', mul_smul]
  exact Submodule.smul_mem_smul ha x.2

/-- 第 n 次成分は `M/I^(n+1)M → M/I^nM` の核である。 -/
noncomputable def gradedPieceEquivKer (n : ℕ) :
    GradedPiece R I M n ≃ₗ[R]
      LinearMap.ker (Submodule.factor (adicSubmodule_succ_le R I M n)) := by
  let f : adicSubmodule R I M n →ₗ[R] M ⧸ adicSubmodule R I M (n + 1) :=
    (adicSubmodule R I M (n + 1)).mkQ.comp (adicSubmodule R I M n).subtype
  have hker : f.ker = gradedDenominator R I M n := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    rfl
  have hrange : f.range = LinearMap.ker
      (Submodule.factor (adicSubmodule_succ_le R I M n)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype,
      Submodule.ker_mapQ, Submodule.comap_id]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

/-- Samuel 関数の増分は第 n 次成分の長さ。無限長も許す。 -/
theorem samuelFunction_succ (n : ℕ) :
    samuelFunction R I M (n + 1) = hilbertFunction R I M n + samuelFunction R I M n := by
  let f := Submodule.factor (adicSubmodule_succ_le R I M n)
  have h := Module.length_eq_add_of_exact f.ker.subtype f
    (Submodule.subtype_injective _) (Submodule.factor_surjective _)
    (LinearMap.exact_subtype_ker_map f)
  change Module.length R (M ⧸ adicSubmodule R I M (n + 1)) =
    Module.length R (GradedPiece R I M n) + Module.length R (M ⧸ adicSubmodule R I M n)
  rw [(gradedPieceEquivKer R I M n).length_eq]
  exact h

lemma samuelFunction_zero : samuelFunction R I M 0 = 0 := by
  simp [samuelFunction]

/-- Samuel 関数は第 0 次から第 n-1 次までの長さの和。 -/
theorem samuelFunction_eq_sum (n : ℕ) :
    samuelFunction R I M n = ∑ i ∈ Finset.range n, hilbertFunction R I M i := by
  induction n with
  | zero => simp [samuelFunction_zero]
  | succ n ih => rw [samuelFunction_succ, ih, Finset.sum_range_succ, add_comm]

section finiteLength

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]

/-- 準素イデアルについて、各次数の商は有限長。 -/
theorem isFiniteLength_gradedPiece (hI : I.radical = maximalIdeal R) (n : ℕ) :
    IsFiniteLength R (GradedPiece R I M n) := by
  have : IsArtinianRing (R ⧸ maximalIdeal R) :=
    inferInstanceAs (IsArtinianRing (ResidueField R))
  have : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_quotient_of_le_radical (maximalIdeal R) I (by rw [hI])
  exact isFiniteLength_of_le_radical_annihilator I _
    ((ideal_le_annihilator_gradedPiece R I M n).trans Ideal.le_radical)

lemma hilbertFunction_ne_top (hI : I.radical = maximalIdeal R) (n : ℕ) :
    hilbertFunction R I M n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (isFiniteLength_gradedPiece R I M hI n)

end finiteLength

end SerrePositivity.HilbertSamuel
