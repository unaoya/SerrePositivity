module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.DirectSum.Module

/-! # 随伴次数加群と Rees 加群

## 概要

`I` 進フィルトレーション `I^n M` の随伴次数加群 `gr_I(M) = ⊕ I^n M / I^{n+1} M` と、
Rees 加群（`I.stableFiltration ⊤` の Rees 化）、その次数付けを構成する。随伴次数加群の各成分が有限長で、
Rees 加群が有限生成であることを示す。

## 方針

フィルトレーションは Mathlib の `Ideal.stableFiltration` に揃え、Rees 加群は `Ideal.Filtration.submodule` を使う。

## 規約

名前空間は `HilbertSamuel`。

## 使われ方

多項式環による表示（`HilbertSamuel/ReesPresentation`）、Hilbert 級数（`HilbertSamuel/Polynomial`）、
正則局所環の生成元の正則性（`RegularLocalRing/Graded`）。
-/

@[expose] public noncomputable section

universe u v w

section Graded

namespace SerrePositivity.HilbertSamuel

open IsLocalRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- I 進フィルトレーションの第 n 段。Mathlib の安定フィルトレーション `I.stableFiltration ⊤` の第 n 段
（定義上 `I ^ n • ⊤`）。 -/
def adicSubmodule (n : ℕ) : Submodule R M := (I.stableFiltration (⊤ : Submodule R M)).N n

lemma adicSubmodule_eq (n : ℕ) : adicSubmodule R I M n = I ^ n • ⊤ := rfl

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

end Graded

section Rees

namespace SerrePositivity.HilbertSamuel

open PolynomialModule
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- `⊕ I^nM t^n`。係数が I 進部分加群に入る多項式加群。 -/
abbrev ReesModule := (I.stableFiltration (⊤ : Submodule R M)).submodule

/-- `⊕ I^(n+1)M t^n` の ambient polynomial module 内での表示。 -/
abbrev shiftedReesModule := (I.stableFiltration (I • (⊤ : Submodule R M))).submodule

/-- `⊕ I^(n+1)M t^n` を Rees 加群内の部分加群として見る。 -/
def reesDenominator : Submodule (reesAlgebra I) (ReesModule R I M) :=
  (shiftedReesModule R I M).comap (ReesModule R I M).subtype

/-- 随伴次数加群の Rees 加群による商表示。 -/
abbrev ReesGraded := ReesModule R I M ⧸ reesDenominator R I M

lemma mem_reesDenominator (f : ReesModule R I M) :
    f ∈ reesDenominator R I M ↔
      ∀ n, (f : PolynomialModule R M).coeff n ∈ adicSubmodule R I M (n + 1) := by
  change (∀ n, f.1.coeff n ∈ I ^ n • (I • (⊤ : Submodule R M))) ↔ _
  simp only [adicSubmodule_eq, pow_succ, mul_smul]

instance reesModule_finite [IsNoetherianRing R] [Module.Finite R M] :
    Module.Finite (reesAlgebra I) (ReesModule R I M) := by
  apply Module.Finite.of_fg
  exact ((I.stableFiltration (⊤ : Submodule R M)).submodule_fg_iff_stable
    (fun _ => IsNoetherian.noetherian _)).mpr (I.stableFiltration_stable _)

instance reesGraded_finite [IsNoetherianRing R] [Module.Finite R M] :
    Module.Finite (reesAlgebra I) (ReesGraded R I M) := inferInstance

/-- 随伴次数加群全体も I で消える。 -/
lemma ideal_le_annihilator_reesGraded :
    I ≤ Module.annihilator R (ReesGraded R I M) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨f, rfl⟩ := (reesDenominator R I M).mkQ_surjective x
  have hf : a • f ∈ reesDenominator R I M := by
    rw [mem_reesDenominator]
    intro n
    change a • f.1.coeff n ∈ I ^ (n + 1) • (⊤ : Submodule R M)
    rw [pow_succ', mul_smul]
    exact Submodule.smul_mem_smul ha (f.2 n)
  exact (((reesDenominator R I M).mkQ.restrictScalars R).map_smul a f).symm.trans
    ((Submodule.Quotient.mk_eq_zero (p := reesDenominator R I M) (x := a • f)).mpr hf)

/-- 作用する Rees 代数でも、係数イデアル I の像は随伴次数加群を消す。 -/
lemma ideal_map_le_annihilator_reesGraded :
    I.map (algebraMap R (reesAlgebra I)) ≤
      Module.annihilator (reesAlgebra I) (ReesGraded R I M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro x
  rw [algebraMap_smul]
  exact (Module.mem_annihilator.mp (ideal_le_annihilator_reesGraded R I M ha)) x

/-- 第 n 次の係数を、部分加群 I^nM の元として取り出す。 -/
def reesCoefficient (n : ℕ) : ReesModule R I M →ₗ[R] adicSubmodule R I M n where
  toFun f := ⟨f.1.coeff n, f.2 n⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 第 n 次成分の元を単項式として Rees 加群へ入れる。 -/
def reesSingle (n : ℕ) : adicSubmodule R I M n →ₗ[R] ReesModule R I M :=
  ((lsingle R n).comp (adicSubmodule R I M n).subtype).codRestrict
    ((ReesModule R I M).restrictScalars R) (by
    intro x i
    simp only [LinearMap.comp_apply, lsingle_apply]
    split_ifs with hi
    · subst i; exact x.2
    · exact Submodule.zero_mem _)

@[simp]
lemma reesCoefficient_reesSingle (n : ℕ) (x : adicSubmodule R I M n) :
    reesCoefficient R I M n (reesSingle R I M n x) = x := by
  apply Subtype.ext
  change (PolynomialModule.lsingle R n (x : M)).coeff n = (x : M)
  simp only [lsingle_apply, ite_true]

/-- 係数を対応する次数の商へ落とす写像。 -/
def gradedCoefficient (n : ℕ) : ReesGraded R I M →ₗ[R] GradedPiece R I M n :=
  ((reesDenominator R I M).restrictScalars R).liftQ
    ((gradedDenominator R I M n).mkQ.comp (reesCoefficient R I M n)) (by
      intro f hf
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (mem_reesDenominator R I M f).mp hf n)

/-- I の元 a に対応する Rees 代数の次数一の元 a t。 -/
def reesDegreeOne (a : I) : reesAlgebra I :=
  ⟨Polynomial.monomial 1 (a : R), reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using a.2)⟩

lemma reesDegreeOne_smul_reesSingle (a : I) (n : ℕ) (x : adicSubmodule R I M n) :
    reesDegreeOne R I a • reesSingle R I M n x =
      reesSingle R I M (n + 1) (adicMultiplication R I M a n x) := by
  apply Subtype.ext
  change Polynomial.monomial 1 (a : R) • PolynomialModule.single R n (x : M) =
    PolynomialModule.single R (n + 1) ((a : R) • (x : M))
  rw [PolynomialModule.monomial_smul_single, Nat.add_comm 1 n]

/-- 第 n 次の商を、単項式の剰余類として随伴次数加群へ入れる。 -/
def gradedSingle (n : ℕ) : GradedPiece R I M n →ₗ[R] ReesGraded R I M :=
  (gradedDenominator R I M n).liftQ
    (((reesDenominator R I M).mkQ.restrictScalars R).comp (reesSingle R I M n)) (by
      intro x hx
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rw [mem_reesDenominator]
      intro j
      change (PolynomialModule.lsingle R n (x : M)).coeff j ∈ _
      rw [lsingle_apply]
      split_ifs with hj
      · subst j; exact hx
      · exact Submodule.zero_mem _)

@[simp]
lemma gradedSingle_mk (n : ℕ) (x : adicSubmodule R I M n) :
    gradedSingle R I M n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (reesSingle R I M n x) := rfl

@[simp]
lemma gradedCoefficient_gradedSingle_self (n : ℕ) (x : GradedPiece R I M n) :
    gradedCoefficient R I M n (gradedSingle R I M n x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (gradedDenominator R I M n).mkQ
    (reesCoefficient R I M n (reesSingle R I M n x)) = _
  rw [reesCoefficient_reesSingle]
  rfl

lemma gradedCoefficient_gradedSingle_ne (n m : ℕ) (hnm : m ≠ n)
    (x : GradedPiece R I M m) :
    gradedCoefficient R I M n (gradedSingle R I M m x) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (gradedDenominator R I M n).mkQ
    (reesCoefficient R I M n (reesSingle R I M m x)) = 0
  have hc : reesCoefficient R I M n (reesSingle R I M m x) = 0 := by
    apply Subtype.ext
    change (PolynomialModule.lsingle R m (x : M)).coeff n = 0
    simp only [PolynomialModule.lsingle_apply, ite_eq_right hnm]
  rw [hc, map_zero]

/-- Rees 代数の次数一の作用は、各商の次数一の乗法と両立する。 -/
lemma reesDegreeOne_smul_gradedSingle (a : I) (n : ℕ) (x : GradedPiece R I M n) :
    reesDegreeOne R I a • gradedSingle R I M n x =
      gradedSingle R I M (n + 1) (gradedMultiplication R I M a n x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [gradedMultiplication_mk, gradedSingle_mk, gradedSingle_mk]
  exact ((reesDenominator R I M).mkQ.map_smul (reesDegreeOne R I a)
    (reesSingle R I M n x)).symm.trans
    (congrArg (reesDenominator R I M).mkQ (reesDegreeOne_smul_reesSingle R I M a n x))

/-- 各次数の商の直和から、Rees 加群による商表示への写像。 -/
def directSumToReesGraded : (⨁ n, GradedPiece R I M n) →ₗ[R] ReesGraded R I M :=
  DirectSum.toModule R ℕ _ (gradedSingle R I M)

lemma gradedCoefficient_comp_directSumToReesGraded (n : ℕ) :
    (gradedCoefficient R I M n).comp (directSumToReesGraded R I M) =
      DirectSum.component R ℕ (GradedPiece R I M) n := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, directSumToReesGraded, DirectSum.toModule_lof]
  by_cases h : m = n
  · subst m; simp
  · rw [gradedCoefficient_gradedSingle_ne R I M n m h]
    change 0 = (DirectSum.of (GradedPiece R I M) m x) n
    exact (DFinsupp.single_eq_of_ne (Ne.symm h)).symm

lemma directSumToReesGraded_injective : Function.Injective (directSumToReesGraded R I M) := by
  intro x y hxy
  apply DFinsupp.ext
  intro n
  have h := congrArg (gradedCoefficient R I M n) hxy
  change (DirectSum.component R ℕ (GradedPiece R I M) n) x =
    (DirectSum.component R ℕ (GradedPiece R I M) n) y
  simpa only [← gradedCoefficient_comp_directSumToReesGraded R I M n,
    LinearMap.comp_apply] using h

lemma reesModule_as_sum (f : ReesModule R I M) :
    f = ∑ n ∈ f.1.coeff.support, reesSingle R I M n ⟨f.1.coeff n, f.2 n⟩ := by
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  simp only [Submodule.coe_sum, PolynomialModule.coeff_sum]
  change f.1.coeff = ∑ n ∈ f.1.coeff.support, Finsupp.single n (f.1.coeff n)
  exact (Finsupp.sum_single _).symm

lemma directSumToReesGraded_surjective : Function.Surjective (directSumToReesGraded R I M) := by
  intro x
  obtain ⟨f, rfl⟩ := (reesDenominator R I M).mkQ_surjective x
  refine ⟨∑ n ∈ f.1.coeff.support, DirectSum.lof R ℕ (GradedPiece R I M) n
    ((gradedDenominator R I M n).mkQ ⟨f.1.coeff n, f.2 n⟩), ?_⟩
  simp only [map_sum, directSumToReesGraded, DirectSum.toModule_lof,
    Submodule.mkQ_apply, gradedSingle_mk]
  change (∑ n ∈ f.1.coeff.support, (reesDenominator R I M).mkQ
    (reesSingle R I M n ⟨f.1.coeff n, f.2 n⟩)) = (reesDenominator R I M).mkQ f
  rw [← map_sum, ← reesModule_as_sum]

/-- `gr_I(M)` の直和表示と Rees 加群の商表示の R 線形同型。 -/
def directSumReesGradedEquiv : (⨁ n, GradedPiece R I M n) ≃ₗ[R] ReesGraded R I M :=
  LinearEquiv.ofBijective (directSumToReesGraded R I M)
    ⟨directSumToReesGraded_injective R I M, directSumToReesGraded_surjective R I M⟩

end SerrePositivity.HilbertSamuel

end Rees
