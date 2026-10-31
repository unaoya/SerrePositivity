module

public import SerrePositivity.PerfectComplex.KoszulLength
public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.PerfectComplex.Free.Euler
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-! # 長さ付き代数の Koszul 有限性と Euler 特性

## 概要

長さ付き代数について Koszul ホモロジーの有限性と正の次数の消滅を独立な条件として定め、Koszul Euler 特性を定義する。通常の長さによる Koszul 有限性と、剰余体への全射による係数環上の通常長さと基底上の長さの同定を与える。

## 方針

有限性を仮定しない等式は、無限長を零へ送る数値規約を両辺で一致させて扱う。

## 規約

正則性・Noether 性・有限拡大・階数公式は要求しない。

## 使われ方

`LengthAlgebra/Perfect`・`KoszulFormula`、Paper の Lemma 3.5。
-/

@[expose] public noncomputable section

universe u

section KoszulPart

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

/-- 正次数の消滅と零次商の有限性から、一つの Koszul 複体の全次数の有限性を得る。 -/
lemma koszul_finite_of_zero_positive
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf z i) = 0)
    (hquot : lam.len (C ⧸ Ideal.span (Set.range z)) ≠ ⊤) (q : ℤ) :
    lam.len ((koszulComplex z).homology q) ≠ ⊤ := by
  apply koszul_finite_of_homologySelf
  intro i
  rcases i with _ | i
  · change lam.len ((koszulComplex z).homology 0) ≠ ⊤
    rwa [lam.len_congr _ _ (koszulComplex_homology_zero_equiv z).some]
  · rw [hzero (i + 1) (by omega)]
    exact ENNReal.zero_ne_top

end SerrePositivity.LengthAlgebra

end KoszulPart

section OrdinaryPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal

/-- パラメータ商が Artin 環なら、各冪の Koszul ホモロジーの通常の長さは有限。 -/
lemma ordinary_koszul_pow_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) [IsArtinianRing (R ⧸ Ideal.span (Set.range z))]
    (v : ℕ) (i : ℤ) :
    (NormalizedLength.ordinary R).len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤ := by
  have : IsArtinianRing (R ⧸ Ideal.span (Set.range (fun j ↦ z j ^ v))) :=
    isArtinianRing_quotient_of_le_radical (Ideal.span (Set.range z)) _
      (le_radical_span_pow z Ideal.le_radical v)
  exact ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr
    (homology_finiteLength_of_isPerfectSupported
      (isPerfectSupported_koszulComplex (fun j ↦ z j ^ v)) i))

/-- Noether 局所環でパラメータの根基が極大イデアルを含めば、通常 Koszul 有限性を満たす。 -/
lemma ordinary_koszul_finite_of_maximal_le_radical
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R)
    (hz : IsLocalRing.maximalIdeal R ≤ (Ideal.span (Set.range z)).radical) :
    LengthAlgebra.KoszulFinite (NormalizedLength.ordinary R) z := by
  have : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) :=
    inferInstanceAs (IsArtinianRing (IsLocalRing.ResidueField R))
  have : IsArtinianRing (R ⧸ Ideal.span (Set.range z)) :=
    isArtinianRing_quotient_of_le_radical (IsLocalRing.maximalIdeal R) _ hz
  exact fun v _ q ↦ ordinary_koszul_pow_finite z v q

end SerrePositivity

end OrdinaryPart

section OrdinaryKoszulEulerPart

namespace SerrePositivity
open CategoryTheory IsLocalRing

/-- 剰余体が同じ局所係数環では、通常の Koszul Euler 数は基底上の評価に等しい。 -/
lemma ordinary_koszulEuler_eq_koszulEulerChar
    {A T : Type u} [CommRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    {e : ℕ} (z : Fin e → A)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T))) :
    LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ z) =
      koszulEulerChar A T z := by
  rw [LengthAlgebra.koszulEuler, ← chiOrd_eq_lambdaEuler_ordinary]
  unfold chiOrd koszulEulerChar
  congr 1
  funext q
  rw [length_restrictScalars_eq hres]

end SerrePositivity

end OrdinaryKoszulEulerPart
