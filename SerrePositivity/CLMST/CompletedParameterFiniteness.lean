module

public import SerrePositivity.CLMST.SelectedParameterEuler
public import SerrePositivity.LengthAlgebra.KoszulModule
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Generators

/-! # 全パラメータ系に対する比較先の長さの有限性

選択した列の正の冪で得た有限性を、零次数の商の全射で元の列へ戻す。
生成イデアルの包含だけを用い、命題4.0.14の長さ公式は使用しない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
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

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 選択した正冪の列の零次の有限性を、元の任意のパラメータ系へ戻す。 -/
theorem completedTensor_stage_parameter_zero_length_ne_top
    (n : ℕ) (y : Fin h → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology 0) ≠ ⊤ := by
  cases h with
  | zero => omega
  | succ r =>
    let : IsLocalRing (Section2.StageAlgebra A D t p n) :=
      Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    obtain ⟨y', k, hspan, hk, hparams, _, _, hfinite⟩ :=
      exists_selected_parameter_euler_comparison A D hinj hres t hdimA hdimD hpos
        ht hsop p htp e he hperf n rfl y hy
    let w := Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)
    have hwJ := completedTensorMaxIdeal_le_stage_parameter_radical A D t p n
      (by
        rw [IsScalarTower.algebraMap_eq A D (Section2.StageAlgebra A D t p n)]
        exact (Section2.stageAlgebra_algebraMap_injective A D t p n).comp hinj) w hparams
    have hle : Ideal.span (Set.range w) ≤ Ideal.span (Set.range y) :=
      (span_last_pow_le y' k hk).trans_eq hspan
    have hSm : Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ w)) ≤
        Ideal.span (Set.range ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)) := by
      have hm := Ideal.map_mono (f := (Section2.stageToCompletedTensor A D t p n).toRingHom) hle
      simpa only [Ideal.map_span, ← Set.range_comp] using hm
    exact ne_top_of_le_ne_top (hfinite 0)
      (LengthAlgebra.lambdaKoszul_homology_zero_le_of_span_le
        (completedTensorLength A D t p _) (RPerfd A D t p hperf)
        (completedTensorMaxIdeal_fg A D t p)
        ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ w)
        ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y) hwJ hSm)

include hinj hres hdimA hdimD hpos ht hsop htp e he in
/-- 全有限段の任意のパラメータ系について、零次数を含む全 Koszul 長さが有限。 -/
theorem completedTensor_stage_parameter_length_ne_top
    (n : ℕ) (y : Fin h → Section2.StageAlgebra A D t p n)
    (hy : let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y) (q : ℤ) :
    (completedTensorLength A D t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (((koszulModuleFunctor ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf))).homology q) ≠ ⊤ := by
  by_cases hq : q = 0
  · subst q
    exact completedTensor_stage_parameter_zero_length_ne_top A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf n y hy
  by_cases hneg : q < 0
  · obtain ⟨g, hg, hEtale⟩ := exists_finite_etale_away A D hinj
    rw [completedTensor_stage_target_koszul_length_eq_zero A D hinj hres t hdimA hdimD
      hpos ht hsop p htp e he hperf g hg hEtale.2 n y hy q hneg]
    exact ENNReal.zero_ne_top
  · let := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X _ q
      (koszulModuleFunctor_isZero_X_of_pos
        ((Section2.stageToCompletedTensor A D t p n).toRingHom ∘ y)
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) (RPerfd A D t p hperf)) q (by omega)))
    rw [NormalizedLength.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top

end SerrePositivity.CLMST
