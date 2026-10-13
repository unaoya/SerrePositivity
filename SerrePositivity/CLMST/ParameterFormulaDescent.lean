module

public import SerrePositivity.CLMST.ParameterLastPowerLength
public import SerrePositivity.CommutativeAlgebra.ParameterLastPowerMultiplicity

/-! # 比較元の Euler 公式から任意のパラメータ商への降下

比較元の Euler 評価の数値公式だけを明示的な前提として分離する。
列の選択、末尾の冪の長さ倍率、重複度の倍率、生成イデアルの同値を使い、
任意の元のパラメータ系の長さ公式へ戻す。
Proposition 4.0.14 の結論を引用として用いない。
-/

@[expose] public noncomputable section
universe u
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
    (hsource : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ v : Fin h → StageAlgebra A D t p n,
        IsSystemOfParameters (StageAlgebra A D t p n) v →
        lambdaEuler (completedTensorLength A D t p
          (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)))
          ((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ v)).obj
            (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
        (HilbertSamuel.multiplicity (StageAlgebra A D t p n)
          (Ideal.span (Set.range v)) (StageAlgebra A D t p n) : ℝ) /
          (stageRank h p n : ℝ))
    (y : Fin h → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (StageAlgebra A D t p n) y) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology 0) =
      ENNReal.ofReal ((HilbertSamuel.multiplicity (StageAlgebra A D t p n)
        (Ideal.span (Set.range y)) (StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ)) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  subst h
  let : IsLocalRing (StageAlgebra A D t p n) :=
    stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  let T := StageAlgebra A D t p n
  let S := (CompletedTower A t p) ⊗[A] D
  let C := RPerfd A D t p hperf
  let M := ModuleCat.of S C
  let lam := completedTensorLength A D t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))
  let φ := (stageToCompletedTensor A D t p n).toRingHom
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
        rw [IsScalarTower.algebraMap_eq A D (StageAlgebra A D t p n)]
        exact (stageAlgebra_algebraMap_injective A D t p n).comp hinj) v hv
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
    (hsource : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ v : Fin h → StageAlgebra A D t p n,
        IsSystemOfParameters (StageAlgebra A D t p n) v →
        lambdaEuler (completedTensorLength A D t p
          (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)))
          ((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ v)).obj
            (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
        (HilbertSamuel.multiplicity (StageAlgebra A D t p n)
          (Ideal.span (Set.range v)) (StageAlgebra A D t p n) : ℝ) /
          (stageRank h p n : ℝ))
    (y : Fin h → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (StageAlgebra A D t p n) y) :
    let C := RPerfd A D t p hperf
    let Q := C ⧸ Ideal.span (Set.range fun j ↦ toRPerfd A D t p hperf n (y j))
    let _ := Module.compHom Q (algebraMap (CompletedTower A t p) C)
    (RootTowerLength.completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len Q =
      ENNReal.ofReal (HilbertSamuel.multiplicity (StageAlgebra A D t p n)
        (Ideal.span (Set.range y)) (StageAlgebra A D t p n) : ℝ) /
        (stageRank h p n : ℝ≥0∞) := by
  have hh := completedTensor_stage_parameter_length_of_source_euler_formula A D hinj hres
    t hdimA hdimD hpos ht hsop p htp e he hperf n hsource y hy
  rw [completedTensorLength,
    LengthAlgebra.length_comap_koszulModuleHomology_zero_quotient] at hh
  have hseq : algebraMap ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf) ∘
      ((stageToCompletedTensor A D t p n).toRingHom ∘ y) =
      fun j ↦ toRPerfd A D t p hperf n (y j) := by
    funext j
    exact stageToCompletedTensor_toMixedPerfectoid A D t p hperf n (y j)
  have hpositive : 0 < (stageRank h p n : ℝ) := by
    apply Nat.cast_pos.mpr
    exact pow_pos (Fact.out : p.Prime).pos _
  rw [hseq, ENNReal.ofReal_div_of_pos hpositive, ENNReal.ofReal_natCast] at hh
  exact hh

end SerrePositivity.CLMST
