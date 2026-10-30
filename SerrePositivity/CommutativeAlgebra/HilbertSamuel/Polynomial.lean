module

public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.ReesPresentation
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.HilbertSeries
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.AssociatedGraded
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Samuel 多項式の存在と次数

## 概要

随伴次数加群の Hilbert 級数が有理式であることから、Samuel 関数 `n ↦ ℓ(M / I^n M)` が十分先で多項式に
なることを示し（`exists_isSamuelPoly`）、その次数を生成元の個数で抑える。累積長さの多項式との比較と、
多項式環による表示が誘導する長さの比較も扱う。

## 方針

`gr_I(M)` の Hilbert 級数に `1/(1 - X)` を掛けると Samuel 関数の級数になり、`(1 - X)^{-s}` 型の有理式の係数は
十分先で多項式になる。

## 規約

名前空間は `HilbertSamuel`（累積長さの比較の一部は `HilbertSerre`）。

## 使われ方

Samuel の次元定理（`HilbertSamuel/Dimension`）、重複度の公式（B2）、正則局所環の表示の単射性。
-/

@[expose] public noncomputable section

universe u v w

section Series

namespace SerrePositivity.HilbertSamuel

open IsLocalRing Polynomial Filter

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- `Σ length(I^nM/I^(n+1)M) X^n`。有限長のとき実際の長さを係数とする。 -/
def hilbertSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((hilbertFunction R I M n).toNat : ℚ)

/-- `Σ length(M/I^nM) X^n`。定数項は零。 -/
def samuelSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((samuelFunction R I M n).toNat : ℚ)

/-- Hilbert 多項式の標準構成は、分母の指数 s+1 に対して次数 s 以下。 -/
lemma natDegree_hilbertPoly_succ_le (Q : ℚ[X]) (s : ℕ) :
    (Polynomial.hilbertPoly Q (s + 1)).natDegree ≤ s := by
  by_cases h : Polynomial.hilbertPoly Q (s + 1) = 0
  · simp [h]
  · rw [Polynomial.natDegree_hilbertPoly_of_ne_zero h]
    omega

section finiteLength

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
variable (hI : I.radical = maximalIdeal R)

include hI

/-- 増分の公式を母関数の等式に書き換える。 -/
theorem one_sub_X_mul_samuelSeries :
    (1 - PowerSeries.X) * samuelSeries R I M = PowerSeries.X * hilbertSeries R I M := by
  ext n
  cases n with
  | zero => simp [samuelSeries, samuelFunction_zero]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      samuelSeries, hilbertSeries, PowerSeries.coeff_mk]
    rw [samuelFunction_succ, ENat.toNat_add
      (hilbertFunction_ne_top R I M hI n) (samuelFunction_ne_top R I hI M n)]
    push_cast
    ring

/-- Samuel 関数の級数は Hilbert 級数に `X/(1-X)` を掛けたもの。 -/
theorem samuelSeries_eq :
    samuelSeries R I M =
      PowerSeries.X * hilbertSeries R I M * (PowerSeries.invOneSubPow ℚ 1).val := by
  have hinv := one_sub_X_mul_invOneSubPow_one
  calc
    samuelSeries R I M =
        ((1 - PowerSeries.X) * samuelSeries R I M) *
          (PowerSeries.invOneSubPow ℚ 1).val := by rw [mul_right_comm, hinv, one_mul]
    _ = _ := by rw [one_sub_X_mul_samuelSeries R I M hI]

/-- Samuel 関数は Hilbert 関数の部分和。 -/
theorem samuelFunction_toNat_eq_sum (n : ℕ) :
    ((samuelFunction R I M n).toNat : ℚ) =
      ∑ i ∈ Finset.range n, ((hilbertFunction R I M i).toNat : ℚ) := by
  induction n with
  | zero => simp [samuelFunction_zero]
  | succ n ih =>
    rw [samuelFunction_succ, ENat.toNat_add (hilbertFunction_ne_top R I M hI n)
      (samuelFunction_ne_top R I hI M n), Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- Hilbert 級数が `Q / (1 - X)^s` なら、次数 `s` 以下の Samuel 多項式がある。部分和の多項式性
（`exists_poly_eventually_eq_partialSum`）を Hilbert 関数に適用する。 -/
theorem exists_isSamuelPoly_of_hilbertSeries (s : ℕ) (Q : ℚ[X])
    (hseries : hilbertSeries R I M = Q * (PowerSeries.invOneSubPow ℚ s).val) :
    ∃ P : ℚ[X], IsSamuelPoly R I M P ∧ P.natDegree ≤ s := by
  obtain ⟨P, hP, hdeg⟩ := exists_poly_eventually_eq_partialSum _ s Q hseries
  refine ⟨P, ?_, hdeg⟩
  filter_upwards [hP] with n hn
  exact ⟨samuelFunction_ne_top R I hI M n, (samuelFunction_toNat_eq_sum R I M hI n).trans hn⟩

end finiteLength



end SerrePositivity.HilbertSamuel

end Series

section Polynomial

namespace SerrePositivity.HilbertSamuel

open DirectSum IsLocalRing Polynomial
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Rees 加群の商の中での第 n 次成分。 -/
def reesGrade (n : ℕ) : Submodule R (ReesGraded R I M) :=
  (gradedSingle R I M n).range

lemma gradedSingle_injective (n : ℕ) : Function.Injective (gradedSingle R I M n) :=
  (show Function.LeftInverse (gradedCoefficient R I M n) (gradedSingle R I M n) from
    gradedCoefficient_gradedSingle_self R I M n).injective

/-- 各次数の実際の商と、全体の中でのその像の同型。 -/
def gradedPieceRangeEquiv (n : ℕ) : GradedPiece R I M n ≃ₗ[R] reesGrade R I M n :=
  LinearEquiv.ofInjective (gradedSingle R I M n) (gradedSingle_injective R I M n)

/-- Rees 加群の商の各次数は内部直和をなす。 -/
theorem isInternal_reesGrade : DirectSum.IsInternal (reesGrade R I M) := by
  apply HilbertSerre.isInternal_of_projections (reesGrade R I M)
    (fun n => (gradedSingle R I M n).comp (gradedCoefficient R I M n))
  · intro n x
    obtain ⟨y, hy⟩ := x.2
    change gradedSingle R I M n (gradedCoefficient R I M n (x : ReesGraded R I M)) = x
    rw [← hy, gradedCoefficient_gradedSingle_self]
  · intro n k hkn x
    obtain ⟨y, hy⟩ := x.2
    change gradedSingle R I M n (gradedCoefficient R I M n (x : ReesGraded R I M)) = 0
    rw [← hy, gradedCoefficient_gradedSingle_ne R I M n k hkn, map_zero]
  · apply top_unique
    intro x hx
    clear hx
    obtain ⟨y, rfl⟩ := directSumToReesGraded_surjective R I M x
    induction y using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of n y =>
      rw [← DirectSum.lof_eq_of R, directSumToReesGraded, DirectSum.toModule_lof]
      exact (le_iSup (reesGrade R I M) n) ⟨y, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

lemma reesPolynomialModule_degree_one {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule I (ReesGraded R I M) z hz
    ∀ (i : Fin s) n, ∀ x ∈ reesGrade R I M n,
      (MvPolynomial.X i : MvPolynomial (Fin s) R) • x ∈ reesGrade R I M (n + 1) := by
  let := reesPolynomialModule I (ReesGraded R I M) z hz
  dsimp only
  intro i n x hx
  obtain ⟨y, rfl⟩ := hx
  let a : I := ⟨z i, hz ▸ Ideal.subset_span (Set.mem_range_self i)⟩
  have hr : reesPresentation R I z hz (MvPolynomial.X i) = reesDegreeOne R I a := by
    apply Subtype.ext
    exact reesPresentation_X R I z hz i
  change (reesPresentation R I z hz (MvPolynomial.X i)) • gradedSingle R I M n y ∈ _
  rw [hr, reesDegreeOne_smul_gradedSingle]
  exact ⟨gradedMultiplication R I M a n y, rfl⟩

/-- Rees 商の次数の長さの級数は、元の I 進 Hilbert 級数そのもの。 -/
lemma lengthSeries_reesGrade :
    HilbertSerre.lengthSeries (reesGrade R I M) = hilbertSeries R I M := by
  ext n
  simp only [HilbertSerre.lengthSeries, hilbertSeries, PowerSeries.coeff_mk,
    hilbertFunction, (gradedPieceRangeEquiv R I M n).length_eq]

/-- I 進随伴次数加群に Hilbert–Serre を適用して、有理型の Hilbert 級数を得る。 -/
theorem exists_rational_hilbertSeries [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (hI : I.radical = maximalIdeal R) {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    ∃ Q : ℚ[X], hilbertSeries R I M = Q * (PowerSeries.invOneSubPow ℚ s).val := by
  let := reesPolynomialModule I (ReesGraded R I M) z hz
  let : IsScalarTower R (MvPolynomial (Fin s) R) (ReesGraded R I M) :=
    reesPolynomialModule_scalarTower I (ReesGraded R I M) z hz
  let : Module.Finite (MvPolynomial (Fin s) R) (ReesGraded R I M) :=
    reesPolynomialModule_finite I (ReesGraded R I M) z hz
  let : Decomposition (reesGrade R I M) := (isInternal_reesGrade R I M).chooseDecomposition
  have hfinite (n : ℕ) : IsFiniteLength R (reesGrade R I M n) :=
    (isFiniteLength_gradedPiece R I M hI n).of_injective
      (f := (gradedPieceRangeEquiv R I M n).symm.toLinearMap)
      (gradedPieceRangeEquiv R I M n).symm.injective
  obtain ⟨Q, hQ⟩ := HilbertSerre.exists_rational_lengthSeries R s (ReesGraded R I M)
    (reesGrade R I M) hfinite (reesPolynomialModule_degree_one R I M z hz)
  exact ⟨Q, (lengthSeries_reesGrade R I M).symm.trans hQ⟩

/-- **Hilbert–Samuel の定理**：`I = (x₁, …, x_s)` が `m` 準素で `M` が有限生成なら、Samuel 関数は
十分大きい `n` で次数 `≤ s` の多項式の値に等しい。`gr_I(M)` の Hilbert 級数が `Q/(1−X)^s`
（`exists_rational_hilbertSeries`）で、部分和の多項式性（`exists_isSamuelPoly_of_hilbertSeries`）による
（Atiyah–Macdonald Prop. 11.4、Thm 11.1）。Samuel 多項式の存在はすべてこの定理を通す。 -/
theorem exists_isSamuelPoly [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I.radical = maximalIdeal R) {s : ℕ} (x : Fin s → R) (hx : I = Ideal.span (Set.range x))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ P : ℚ[X], IsSamuelPoly R I M P ∧ P.natDegree ≤ s := by
  obtain ⟨Q, hQ⟩ := exists_rational_hilbertSeries R I M hI x hx.symm
  exact exists_isSamuelPoly_of_hilbertSeries R I M hI s Q hQ

end SerrePositivity.HilbertSamuel

end Polynomial

section Cumulative

namespace SerrePositivity.HilbertSerre

/-- An additive decomposition is unchanged by restricting module scalars. -/
@[instance_reducible]
def decompositionRestrictScalars
    (R : Type u) [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (N : ℕ → Submodule S M) [DirectSum.Decomposition N] :
    DirectSum.Decomposition (fun n => (N n).restrictScalars R) where
  decompose' := DirectSum.decompose N
  left_inv := (DirectSum.decompose N).left_inv
  right_inv := (DirectSum.decompose N).right_inv

/-- The homogeneous polynomial grading is still a decomposition over a smaller scalar ring. -/
@[instance_reducible]
def homogeneousDecompositionRestrictScalars
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (σ : Type w) :
    DirectSum.Decomposition
      (fun n => (MvPolynomial.homogeneousSubmodule σ S n).restrictScalars R) := by
  let : DirectSum.Decomposition (MvPolynomial.homogeneousSubmodule σ S) :=
    MvPolynomial.decomposition
  exact decompositionRestrictScalars R (MvPolynomial.homogeneousSubmodule σ S)

end SerrePositivity.HilbertSerre

namespace SerrePositivity.HilbertSamuel

open IsLocalRing

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The cumulative series of the Rees grades is exactly the Samuel series. -/
theorem cumulativeSeries_reesGrade (hI : I.radical = maximalIdeal R) :
    HilbertSerre.cumulativeSeries (reesGrade R I M) = samuelSeries R I M := by
  rw [HilbertSerre.cumulativeSeries_eq, lengthSeries_reesGrade,
    ← samuelSeries_eq R I M hI]

/-- Summing all graded lengths below degree `n` gives the rational Samuel length. -/
theorem cumulativeLength_reesGrade (hI : I.radical = maximalIdeal R) (n : ℕ) :
    HilbertSerre.cumulativeLength (reesGrade R I M) n =
      ((samuelFunction R I M n).toNat : ℚ) := by
  have h := congrArg (PowerSeries.coeff n) (cumulativeSeries_reesGrade R I M hI)
  simpa only [HilbertSerre.cumulativeSeries, samuelSeries, PowerSeries.coeff_mk] using h

end SerrePositivity.HilbertSamuel

end Cumulative

section PresentationMap

namespace SerrePositivity.HilbertSamuel

open Polynomial IsLocalRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I)

/-- The polynomial presentation, viewed as an `R`-linear map into the self
associated graded module. -/
def gradedPresentationMap :
    MvPolynomial (Fin s) (R ⧸ I) →ₗ[R] ReesGraded R I R :=
  ((reesGradedSelfEquiv R I).symm.toLinearMap.restrictScalars R).comp
    ((gradedReesPresentation R I z hz).toLinearMap.restrictScalars R)

/-- The linear presentation is surjective. -/
theorem gradedPresentationMap_surjective : Function.Surjective (gradedPresentationMap R I z hz) :=
  (reesGradedSelfEquiv R I).symm.surjective.comp
    (gradedReesPresentation_surjective R I z hz)

private theorem prod_monomial {ι : Type*} (t : Finset ι) (d : ι → ℕ) (a : ι → R) :
    (∏ i ∈ t, monomial (d i) (a i)) = monomial (∑ i ∈ t, d i) (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [hi, ih, monomial_mul_monomial]

/-- A monomial of degree `d.degree` evaluates to a Rees monomial in that degree. -/
theorem reesPresentation_monomial_coe (d : Fin s →₀ ℕ) (a : R) :
    (reesPresentation R I z hz (MvPolynomial.monomial d a) : R[X]) =
      monomial d.degree (a * d.prod fun i k => z i ^ k) := by
  change MvPolynomial.aeval (R := R) (fun i => monomial 1 (z i))
    (MvPolynomial.monomial d a) = _
  rw [MvPolynomial.aeval_monomial]
  simp only [algebraMap_apply, monomial_pow, one_mul, Finsupp.prod, prod_monomial,
    C_mul_monomial]
  rfl

/-- The image of a polynomial monomial belongs to its corresponding Rees grade. -/
theorem gradedPresentationMap_monomial_mem (d : Fin s →₀ ℕ) (c : R ⧸ I) :
    gradedPresentationMap R I z hz (MvPolynomial.monomial d c) ∈
      reesGrade R I R d.degree := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  let b := reesPresentation R I z hz (MvPolynomial.monomial d a)
  have hb : a * d.prod (fun i k => z i ^ k) ∈ I ^ d.degree := by
    have hb := b.2 d.degree
    rw [show (b : R[X]) = monomial d.degree (a * d.prod fun i k => z i ^ k)
      from reesPresentation_monomial_coe R I z hz d a, coeff_monomial_same] at hb
    exact hb
  let v : adicSubmodule R I R d.degree :=
    ⟨a * d.prod (fun i k => z i ^ k), by
      simpa only [adicSubmodule_eq, Ideal.smul_eq_mul, Ideal.mul_top] using hb⟩
  have hv : reesModuleSelfEquiv R I (reesSingle R I R d.degree v) = b := by
    apply Subtype.ext
    rw [reesModuleSelfEquiv_reesSingle, reesPresentation_monomial_coe]
  refine ⟨Submodule.Quotient.mk v, ?_⟩
  apply (reesGradedSelfEquiv R I).injective
  rw [reesGradedSelfEquiv_gradedSingle_mk, hv]
  change Ideal.Quotient.mk _ b = reesGradedSelfEquiv R I
    ((reesGradedSelfEquiv R I).symm
      (gradedReesPresentation R I z hz (MvPolynomial.monomial d (Ideal.Quotient.mk I a))))
  rw [LinearEquiv.apply_symm_apply]
  symm
  simpa only [MvPolynomial.map_monomial] using
    gradedReesPresentation_map R I z hz (MvPolynomial.monomial d a)

/-- The presentation preserves every homogeneous degree. -/
theorem gradedPresentationMap_mem_reesGrade (n : ℕ)
    (p : MvPolynomial (Fin s) (R ⧸ I))
    (hp : p ∈ (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n).restrictScalars R) :
    gradedPresentationMap R I z hz p ∈ reesGrade R I R n := by
  classical
  change p.IsHomogeneous n at hp
  rw [MvPolynomial.as_sum p, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hdn : d.degree = n := (hp.degree_eq_sum_deg_support hd).symm
  rw [← hdn]
  exact gradedPresentationMap_monomial_mem R I z hz d (p.coeff d)

/-- The degreewise lengths over `R` agree with those over the quotient
coefficient ring, since its algebra map is surjective. -/
theorem homogeneousSubmodule_length_restrictScalars (s n : ℕ) :
    Module.length R ((MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n).restrictScalars R) =
      Module.length (R ⧸ I) (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n) := by
  change Module.length R (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n) = _
  exact Module.length_eq_of_surjective (S := R) (R := R ⧸ I)
    (Ideal.Quotient.mk_surjective (I := I))

end SerrePositivity.HilbertSamuel

end PresentationMap
