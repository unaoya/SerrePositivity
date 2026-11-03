module

public import SerrePositivity.CLMST.ParameterQuotientLength
public import SerrePositivity.LengthAlgebra.KoszulModule
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Generators
public import SerrePositivity.CLMST.Algebra
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Formula
public import SerrePositivity.CommutativeAlgebra.RootTower.BaseChange
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Basic
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite

/-! # Claim 4.0.15 とパラメータ商の長さの公式

## 概要

最後のパラメータの冪による長さの倍率（Claim 4.0.15、`completedTower_stage_parameter_quotient_last_pow_length`）を示し、比較元の Euler 公式から任意のパラメータ商の長さの公式へ降ろす。一般の段の公式（`proposition_4_0_14`）を零段のパラメータ系へ当て、正則な基底の階数の公式（`base_parameter_quotient_length_eq_rank`）を導く。

## 方針

全パラメータ系の長さの有限性と負の次数の長さの消滅を別々に当て、共通の Koszul Euler 評価の冪の倍率を正規化長さの倍率へ戻す。零段の同型に沿って Samuel 関数と重複度を移す。

## 規約

CLMST Claim 4.0.15・Prop 4.0.14（v4、https://arxiv.org/html/2209.04046v4）。旧 `Inputs.proposition_4_0_14` は名前空間 `CLMST` に移した。旧 `CLMST/ParameterLastPowerLength`・`ParameterFormulaDescent`・`ParameterLength`・`Inputs/ParameterLength`。

## 使われ方

Paper（Theorem 2.5 の混標数、`MixedChar`）。
-/

@[expose] public noncomputable section

universe u

section ParameterLastPowerLengthPart

open scoped TensorProduct ENNReal
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

include hinj hres hdimA hdimD hpos ht hsop htp e he

set_option maxHeartbeats 600000 in
-- 二つの大きな係数モデルと各正冪の有限性を照合するため、型検査の予算を増やす。
/-- 有限段のパラメータ系の最後を正の k 乗にすると、係数 Koszul モデルの零次長さは k 倍。
引用からの高次消滅、独立に証明した有限性、共通の Euler 倍率を組み合わせる。 -/
theorem completedTensor_stage_parameter_last_pow_length
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) (k : ℕ) (hk : 0 < k) :
    let lam := completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
    let φ := (Section2.stageToCompletedTensor A D t p n).toRingHom
    let S := (CompletedTower A t p) ⊗[A] D
    let M := ModuleCat.of S (RPerfd A D t p hperf)
    lam.len (((koszulModuleFunctor
      (φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ k))).obj M).homology 0) =
      (k : ℝ≥0∞) * lam.len (((koszulModuleFunctor (φ ∘ y)).obj M).homology 0) := by
  subst h
  let : IsLocalRing (Section2.StageAlgebra A D t p n) :=
    Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  let lam := completedTensorLength A D t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
  let φ := (Section2.stageToCompletedTensor A D t p n).toRingHom
  let S := (CompletedTower A t p) ⊗[A] D
  let M := ModuleCat.of S (RPerfd A D t p hperf)
  let w := φ ∘ y
  have hmap (j : ℕ) : φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ j) =
      Fin.snoc (Fin.init w) (w (Fin.last r) ^ j) := by
    rw [Fin.comp_snoc]
    congr 1
    exact φ.map_pow _ _
  have hfinite (j : ℕ) (hj : 0 < j) (q : ℤ) :
      lam.len (((koszulModuleFunctor (Fin.snoc (Fin.init w)
        (w (Fin.last r) ^ j))).obj M).homology q) ≠ ⊤ := by
    have hh := completedTensor_stage_parameter_length_ne_top A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf n _ (hy.pow_last j hj) q
    rw [hmap j] at hh
    exact hh
  have hnegative (j : ℕ) (hj : 0 < j) (q : ℤ) (hq : q < 0) :
      lam.len (((koszulModuleFunctor (Fin.snoc (Fin.init w)
        (w (Fin.last r) ^ j))).obj M).homology q) = 0 := by
    have hh := completedTensor_stage_target_koszul_length_eq_zero A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf g hg hEtale n _ (hy.pow_last j hj) q hq
    rw [hmap j] at hh
    exact hh
  have htor (j : ℕ) (hj : 0 < j) (q : ℤ) :
      IsPowTorsion (completedTensorMaxIdeal A D t p)
        (((koszulModuleFunctor (Fin.snoc (Fin.init w)
          (w (Fin.last r) ^ j))).obj M).homology q) := by
    have hJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
      (by
        rw [IsScalarTower.algebraMap_eq A D (Section2.StageAlgebra A D t p n)]
        exact (Section2.stageAlgebra_algebraMap_injective A D t p n).comp hinj)
      _ (hy.pow_last j hj)
    rw [hmap j] at hJ
    exact isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p)
      _ hJ M q
  have he := length_koszulModule_zero_last_pow lam (Fin.init w) (w (Fin.last r))
    M htor hfinite hnegative k hk
  change lam.len (((koszulModuleFunctor
    (φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ k))).obj M).homology 0) =
      (k : ℝ≥0∞) * lam.len (((koszulModuleFunctor w).obj M).homology 0)
  rw [Fin.snoc_init_self] at he
  rw [hmap k]
  exact he

set_option maxHeartbeats 600000 in
-- 係数制限の二つの作用と具体的な商の型を照合するため、型検査の予算を増やす。
/-- CLMST Claim 4.0.15 の実際の商の形：最後のパラメータの正冪により長さは指数倍。
長さは完備塔上で測り、商への作用と有限段からの写像を明示する。 -/
theorem completedTower_stage_parameter_quotient_last_pow_length
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (n : ℕ) {r : ℕ} (hr : h = r + 1) (y : Fin (r + 1) → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) (k : ℕ) (hk : 0 < k) :
    let C := RPerfd A D t p hperf
    let φ := (toRPerfd A D t p hperf n).toRingHom
    let Qpow := C ⧸ Ideal.span
      (Set.range (φ ∘ Fin.snoc (Fin.init y) (y (Fin.last r) ^ k)))
    let Q := C ⧸ Ideal.span (Set.range (φ ∘ y))
    let _ := Module.compHom Qpow (algebraMap (CompletedTower A t p) C)
    let _ := Module.compHom Q (algebraMap (CompletedTower A t p) C)
    let lam := RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
    lam.len Qpow = (k : ℝ≥0∞) * lam.len Q := by
  have hh := completedTensor_stage_parameter_last_pow_length A D hinj hres t hdimA hdimD
    hpos ht hsop p htp e he hperf g hg hEtale n hr y hy k hk
  dsimp only [completedTensorLength] at hh
  rw [LengthAlgebra.length_comap_koszulModuleHomology_zero_quotient,
    LengthAlgebra.length_comap_koszulModuleHomology_zero_quotient] at hh
  have hseq (v : Fin (r + 1) → Section2.StageAlgebra A D t p n) :
      algebraMap ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf) ∘
        ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ v) =
        (toRPerfd A D t p hperf n).toRingHom ∘ v := by
    funext j
    exact stageToCompletedTensor_toMixedPerfectoid A D t p hperf n (v j)
  rw [hseq, hseq] at hh
  exact hh

end SerrePositivity.CLMST

end ParameterLastPowerLengthPart

section ParameterFormulaDescentPart

open scoped TensorProduct ENNReal
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory
variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

include hinj hres hdimA hdimD hpos ht hsop htp e he

set_option maxHeartbeats 1000000 in
-- 全段の複数の Koszul モデルと有限性の証明を照合するため、型検査の予算を増やす。
/-- 比較元の Euler 公式から、全パラメータ系の係数モデルの零次長さの公式を導く。
数値的な比較元の評価は独立した明示的な入力として残す。 -/
theorem completedTensor_stage_parameter_length_of_source_euler_formula
    (n : ℕ)
    (hsource : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ v : Fin h → Section2.StageAlgebra A D t p n,
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) v →
        lambdaEuler (completedTensorLength A D t p
          (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)))
          ((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ v)).obj
            (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
        (HilbertSamuel.multiplicity (Section2.StageAlgebra A D t p n)
          (Ideal.span (Set.range v)) (Section2.StageAlgebra A D t p n) : ℝ) /
          (stageRank h p n : ℝ))
    (y : Fin h → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology 0) =
      ENNReal.ofReal ((HilbertSamuel.multiplicity (Section2.StageAlgebra A D t p n)
        (Ideal.span (Set.range y)) (Section2.StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ)) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  subst h
  let : IsLocalRing (Section2.StageAlgebra A D t p n) :=
    Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  let T := Section2.StageAlgebra A D t p n
  let S := (CompletedTower A t p) ⊗[A] D
  let C := RPerfd A D t p hperf
  let M := ModuleCat.of S C
  let lam := completedTensorLength A D t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
  let φ := (Section2.stageToCompletedTensor A D t p n).toRingHom
  obtain ⟨y', k, hspan, hk, hparam, hcompare⟩ :=
    exists_selected_parameter_euler_comparison A D hinj hres t hdimA hdimD hpos ht hsop
      p htp e he hperf n rfl y hy
  have hy' : IsSystemOfParameters T y' := by
    refine ⟨hy.1, ?_⟩
    rw [hspan]
    exact hy.2
  let w := Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)
  obtain ⟨g, hg, _, hEtale⟩ := exists_finite_etale_away A D hinj
  have hnegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor (φ ∘ w)).obj M).homology q) = 0 := by
    intro q hq
    exact completedTensor_stage_target_koszul_length_eq_zero A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf g hg hEtale n w hparam q hq
  have hpow := completedTensor_stage_parameter_last_pow_length A D hinj hres t hdimA hdimD
    hpos ht hsop p htp e he hperf g hg hEtale n rfl y' hy' k hk
  have hnum : (lam.len (((koszulModuleFunctor (φ ∘ w)).obj M).homology 0)).toReal =
      (HilbertSamuel.multiplicity T (Ideal.span (Set.range w)) T : ℝ) /
        (stageRank (r + 1) p n : ℝ) := by
    rw [← lambdaEuler_koszulModule_eq_zero_homology_length lam _ M hnegative]
    exact hcompare.2.1.trans (hsource w hparam)
  have hmul : (HilbertSamuel.multiplicity T (Ideal.span (Set.range w)) T : ℝ) =
      (k : ℝ) * (HilbertSamuel.multiplicity T (Ideal.span (Set.range y')) T : ℝ) := by
    exact_mod_cast HilbertSamuel.multiplicity_parameter_last_pow T y' hy' k hk
  rw [hmul, mul_div_assoc] at hnum
  have hpowR := congrArg ENNReal.toReal hpow
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hpowR
  have hbaseR : (lam.len (((koszulModuleFunctor (φ ∘ y')).obj M).homology 0)).toReal =
      (HilbertSamuel.multiplicity T (Ideal.span (Set.range y')) T : ℝ) /
        (stageRank (r + 1) p n : ℝ) := by
    exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hk) (hpowR.symm.trans hnum)
  have hgen : Ideal.span (Set.range (φ ∘ y')) = Ideal.span (Set.range (φ ∘ y)) := by
    rw [Set.range_comp, Set.range_comp, ← Ideal.map_span, ← Ideal.map_span, hspan]
  have hJ (v : Fin (r + 1) → T) (hv : IsSystemOfParameters T v) :
      completedTensorMaxIdeal A D t p ≤ (Ideal.span (Set.range (φ ∘ v))).radical :=
    completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
      (by
        rw [IsScalarTower.algebraMap_eq A D (Section2.StageAlgebra A D t p n)]
        exact (Section2.stageAlgebra_algebraMap_injective A D t p n).comp hinj) v hv
  have heq : lam.len (((koszulModuleFunctor (φ ∘ y')).obj M).homology 0) =
      lam.len (((koszulModuleFunctor (φ ∘ y)).obj M).homology 0) := by
    apply le_antisymm
    · exact LengthAlgebra.lambdaKoszul_homology_zero_le_of_span_le lam C
        (completedTensorMaxIdeal_fg A D t p) (φ ∘ y) (φ ∘ y') (hJ y hy) hgen.ge
    · exact LengthAlgebra.lambdaKoszul_homology_zero_le_of_span_le lam C
        (completedTensorMaxIdeal_fg A D t p) (φ ∘ y') (φ ∘ y) (hJ y' hy') hgen.le
  rw [hspan, heq] at hbaseR
  have hfinite := completedTensor_stage_parameter_length_ne_top A D hinj hres t hdimA hdimD
    hpos ht hsop p htp e he hperf n y hy 0
  change lam.len (((koszulModuleFunctor (φ ∘ y)).obj M).homology 0) = _
  rw [← hbaseR, ENNReal.ofReal_toReal hfinite]

set_option maxHeartbeats 600000 in
-- 完備塔作用を持つ商と係数 Koszul モデルを照合するため、型検査の予算を増やす。
/-- 比較元の独立した Euler 公式から、Proposition 4.0.14 の実際の商の式を導く。
出力は原典と同じ、重複度の ofReal を有限段の階数で割る形である。 -/
theorem completedTower_stage_parameter_quotient_length_of_source_euler_formula
    (n : ℕ)
    (hsource : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ v : Fin h → Section2.StageAlgebra A D t p n,
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) v →
        lambdaEuler (completedTensorLength A D t p
          (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)))
          ((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ v)).obj
            (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
        (HilbertSamuel.multiplicity (Section2.StageAlgebra A D t p n)
          (Ideal.span (Set.range v)) (Section2.StageAlgebra A D t p n) : ℝ) /
          (stageRank h p n : ℝ))
    (y : Fin h → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) :
    let C := RPerfd A D t p hperf
    let Q := C ⧸ Ideal.span (Set.range fun j ↦ toRPerfd A D t p hperf n (y j))
    let _ := Module.compHom Q (algebraMap (CompletedTower A t p) C)
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len Q =
      ENNReal.ofReal (HilbertSamuel.multiplicity (Section2.StageAlgebra A D t p n)
        (Ideal.span (Set.range y)) (Section2.StageAlgebra A D t p n) : ℝ) /
        (stageRank h p n : ℝ≥0∞) := by
  have hh := completedTensor_stage_parameter_length_of_source_euler_formula A D hinj hres
    t hdimA hdimD hpos ht hsop p htp e he hperf n hsource y hy
  rw [completedTensorLength,
    LengthAlgebra.length_comap_koszulModuleHomology_zero_quotient] at hh
  have hseq : algebraMap ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf) ∘
      ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y) =
      fun j ↦ toRPerfd A D t p hperf n (y j) := by
    funext j
    exact stageToCompletedTensor_toMixedPerfectoid A D t p hperf n (y j)
  have hpositive : 0 < (stageRank h p n : ℝ) := by
    apply Nat.cast_pos.mpr
    exact pow_pos (Fact.out : p.Prime).pos _
  rw [hseq, ENNReal.ofReal_div_of_pos hpositive, ENNReal.ofReal_natCast] at hh
  exact hh

end SerrePositivity.CLMST

end ParameterFormulaDescentPart

section ParameterLengthPart

namespace SerrePositivity.CLMST
open IsLocalRing Section2
open scoped ENNReal

/-- CLMST Proposition 4.0.14：任意の有限段のパラメータ商に対する長さ・重複度の公式。
`stageRank h p n=p^(nh)` の逆数を保ち、商には有限段からの標準 D 代数写像を用いる。 -/
theorem proposition_4_0_14
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (n : ℕ) :
    let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    ∀ (y : Fin h → Section2.StageAlgebra A D t p n),
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y →
      let _ := Module.compHom
        ((RPerfd A D t p hperf) ⧸
          Ideal.span (Set.range fun j ↦ toRPerfd A D t p hperf n (y j)))
        (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
      (RootTowerLength.completedNormalizedLength A t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
        ((RPerfd A D t p hperf) ⧸
          Ideal.span (Set.range fun j ↦ toRPerfd A D t p hperf n (y j))) =
        ENNReal.ofReal
          (HilbertSamuel.multiplicity (Section2.StageAlgebra A D t p n) (Ideal.span (Set.range y))
            (Section2.StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ≥0∞) := by
  let := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  dsimp only
  intro y hy
  have htA : ∀ i, t i ∈ maximalIdeal A :=
    fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)
  have hp : (p : A) ∈ maximalIdeal A := by
    rw [← htp]
    exact htA _
  have htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D := by
    intro i
    rw [← hsop.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  exact completedTower_stage_parameter_quotient_length_of_source_euler_formula
    A D hinj hres t hdimA hdimD hpos ht hsop p htp e he hperf n (by
      dsimp only
      intro v hv
      exact completedTensor_stage_source_euler_eq_multiplicity
        A D t p htA hp htD hres n v hv) y hy

end SerrePositivity.CLMST

end ParameterLengthPart

section ParameterLengthPart

namespace SerrePositivity.CLMST
open IsLocalRing Section2
open scoped ENNReal

variable (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- D のパラメータ系を任意の有限段へ移し、同じ商の長さをその段の重複度で評価する。
有限段の局所性やパラメータの移送を利用者に仮定として要求しない。 -/
theorem parameter_quotient_length_at_stage (n : ℕ)
    (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j))) =
      ENNReal.ofReal
        (HilbertSamuel.multiplicity (Section2.StageAlgebra A D t p n)
          (Ideal.span (Set.range (algebraMap D (Section2.StageAlgebra A D t p n) ∘ z)))
          (Section2.StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ≥0∞) := by
  have hzN := Section2.isSystemOfParameters_stageAlgebra A D t p hsop n z hz
  have hlen := proposition_4_0_14 A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf n (algebraMap D _ ∘ z) hzN
  have hseq : (fun j ↦ toRPerfd A D t p hperf n
      ((algebraMap D (Section2.StageAlgebra A D t p n) ∘ z) j)) =
      (fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)) := by
    funext j
    exact toRPerfd_algebraMap_D A D t p hperf n (z j)
  rw [hseq] at hlen
  exact hlen

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 一般段の公式を零段へ適用し、D のパラメータ商の長さを重複度に同定する。 -/
theorem parameter_quotient_length
    (z : Fin h → D) (hz : IsSystemOfParameters D z) :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j)))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (z j))) =
      ENNReal.ofReal (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
  have hlen := parameter_quotient_length_at_stage A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf 0 z hz
  have hsymm : (⇑(Section2.stage0Equiv A D t p).symm.toRingEquiv : D → Section2.StageAlgebra A D t p 0) =
      algebraMap D (Section2.StageAlgebra A D t p 0) := by
    funext d
    apply (Section2.stage0Equiv A D t p).injective
    simp
  have hm := HilbertSamuel.multiplicity_span_map_ringEquiv
    (Section2.stage0Equiv A D t p).symm.toRingEquiv z
  rw [hsymm] at hm
  rw [hm] at hlen
  simpa only [stageRank, Nat.zero_mul, pow_zero, Nat.cast_one, div_one] using hlen

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- Prop 4.0.14 の「特に」の階数公式は、零段の商比較と証明済みの重複度公式から従う。 -/
theorem base_parameter_quotient_length_eq_rank :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j))))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j)))) =
      (Module.finrank A D : ℝ≥0∞) := by
  have hlen := parameter_quotient_length A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf (algebraMap A D ∘ t) hsop
  rw [HilbertSamuel.multiplicity_eq_rank_of_regular_base A D hinj hres t ht hdimA hsop] at hlen
  simpa only [Function.comp_apply, Rat.cast_natCast, ENNReal.ofReal_natCast] using hlen

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 原典の特別な公式を、m_A を C に拡大したイデアルによる商そのもので述べる。 -/
theorem base_maximalIdeal_quotient_length_eq_rank :
    let _ := Module.compHom
      ((RPerfd A D t p hperf) ⧸
        (maximalIdeal A).map (algebraMap A (RPerfd A D t p hperf)))
      (algebraMap (CompletedTower A t p) (RPerfd A D t p hperf))
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      ((RPerfd A D t p hperf) ⧸
        (maximalIdeal A).map (algebraMap A (RPerfd A D t p hperf))) =
      (Module.finrank A D : ℝ≥0∞) := by
  have hs : algebraMap A (RPerfd A D t p hperf) ∘ t =
      (fun j ↦ algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j))) := by
    funext j
    exact IsScalarTower.algebraMap_apply A D (RPerfd A D t p hperf) (t j)
  have hI : (maximalIdeal A).map (algebraMap A (RPerfd A D t p hperf)) =
      Ideal.span (Set.range fun j ↦
        algebraMap D (RPerfd A D t p hperf) (algebraMap A D (t j))) := by
    rw [← ht, Ideal.map_span, ← Set.range_comp, hs]
  rw [hI]
  exact base_parameter_quotient_length_eq_rank A D hinj hres t hdimA hdimD hpos ht hsop
    p htp e he hperf

end SerrePositivity.CLMST

end ParameterLengthPart
