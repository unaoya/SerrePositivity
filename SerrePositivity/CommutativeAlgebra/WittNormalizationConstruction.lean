module

public import SerrePositivity.CommutativeAlgebra.WittNormalizationBase
public import SerrePositivity.CommutativeAlgebra.WittCoefficientConstruction
public import SerrePositivity.CommutativeAlgebra.MixedCharacteristicParameters
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Eval
public import SerrePositivity.CommutativeAlgebra.FiniteNormalization
public import SerrePositivity.CommutativeAlgebra.WittPowerSeries

/-! # 混標数Cohen正規化の実構成

実際のWitt係数写像とpを含むパラメータを冪級数評価で接続する。
同じ評価の閉ファイバーの有限性と基底の完備性から有限性を証明する。
-/

public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- Witt係数と指定パラメータを評価し、有限な環写像を構成する。
係数写像の存在やパラメータ選択と区別した、実構成の接続定理。 -/
theorem exists_finite_wittPowerSeries_map_of_parameters
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    (φ : WittVector p (ResidueField D) →+* D)
    (hφ : (residue D).comp φ = WittVector.constantCoeff)
    {h : ℕ} (hpos : 0 < h) (z : Fin h → D) (hz0 : z ⟨0, hpos⟩ = (p : D))
    (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ F : MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0}
        (WittVector p (ResidueField D)) →+* D,
      F.Finite ∧ Function.Surjective ((residue D).comp F) ∧
        ∀ i, F (wittPowerSeriesParameter (ResidueField D) p i) = z i := by
  classical
  let W := WittVector p (ResidueField D)
  let σ := {i : Fin h // (i : ℕ) ≠ 0}
  let A := MvPowerSeries σ W
  let J := Ideal.span (Set.range z)
  have hJm : J ≤ maximalIdeal D := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hzm i
  let : IsAdicComplete J D := isAdicComplete_finite_of_le_maximalIdeal J hJm
  let x : σ → D := fun i ↦ z i.val
  have hx (i : σ) : x i ∈ J := Ideal.subset_span (Set.mem_range_self i.val)
  let F : A →+* D := adicPowerSeriesEval φ J x hx
  have ht (i : Fin h) : F (wittPowerSeriesParameter (ResidueField D) p i) = z i := by
    by_cases hi : (i : ℕ) = 0
    · have he : i = ⟨0, hpos⟩ := Fin.ext hi
      subst i
      rw [wittPowerSeriesParameter_zero, map_natCast, hz0]
    · rw [wittPowerSeriesParameter_nonzero _ _ i hi]
      exact adicPowerSeriesEval_X φ J x hx ⟨i, hi⟩
  have hφres : Function.Surjective ((residue D).comp φ) := by
    rw [hφ]
    exact WittVector.constantCoeff_surjective p
  have hres : Function.Surjective ((residue D).comp F) := by
    intro a
    obtain ⟨w, hw⟩ := hφres a
    refine ⟨MvPowerSeries.C w, ?_⟩
    change residue D (adicPowerSeriesEval φ J x hx (MvPowerSeries.C w)) = a
    rw [adicPowerSeriesEval_C]
    exact hw
  let : Algebra W D := φ.toAlgebra
  let : Module.Finite W (D ⧸ J) := finite_quotient_of_common_residue_primary hφres J hprimary
  let : IsAdicComplete (maximalIdeal W) W := by
    rw [(WittVector.irreducible p).maximalIdeal_eq]
    infer_instance
  let : IsAdicComplete (maximalIdeal A) A := isAdicComplete_powerSeries_maximalIdeal σ W
  have hmap : (maximalIdeal A).map F = J := by
    rw [← span_wittPowerSeriesParameter_eq_maximalIdeal hpos (ResidueField D) p,
      Ideal.map_span, ← Set.range_comp]
    exact congrArg Ideal.span (congrArg Set.range (funext ht))
  have hfinite : F.Finite := adicPowerSeriesEval_finite J x hx (maximalIdeal A) hmap
  exact ⟨F, hfinite, hres, ht⟩

/-- 完全剰余体の完備Noether混標数局所整域に対するCohen正規化。
基底は引用3と同じ実際のWitt係数冪級数環であり、有限性と単射性を証明する。 -/
theorem exists_cohen_normalization_mixedCharacteristic
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [CharZero D] [IsAdicComplete (maximalIdeal D) D]
    {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsRegularLocalRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : Algebra A D),
      Function.Injective (algebraMap A D) ∧ Module.Finite A D ∧
      Function.Surjective ((residue D).comp (algebraMap A D)) ∧
      ∃ (t : Fin h → A)
        (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D))),
        Ideal.span (Set.range t) = maximalIdeal A ∧ t ⟨0, hpos⟩ = (p : A) ∧
        ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩ := by
  obtain ⟨φ, hφ⟩ := exists_wittVector_residue_lift D p
  obtain ⟨z, hz0, hzm, hz⟩ := exists_mixedCharacteristic_systemOfParameters D p hdim hpos
  obtain ⟨F, hF, hres, _⟩ := exists_finite_wittPowerSeries_map_of_parameters D p φ hφ
    hpos z hz0 hzm hz.2
  let A := MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D))
  let : IsRegularLocalRing A := isRegularLocalRing_wittPowerSeries _ _ p
  let : IsAdicComplete (maximalIdeal A) A := by
    rw [wittPowerSeries_maximalIdeal_eq]
    exact isAdicComplete_wittPowerSeries_p_sup_variables _ _ p
  let : Algebra A D := F.toAlgebra
  have hinj : Function.Injective F := ringHom_injective_of_finite_of_equal_dimension F hF
    (ringKrullDim_wittNormalizationBase hpos (ResidueField D) p) hdim
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hinj, hF, hres, wittPowerSeriesParameter (ResidueField D) p, RingEquiv.refl A,
    span_wittPowerSeriesParameter_eq_maximalIdeal hpos _ p,
    wittPowerSeriesParameter_zero hpos _ p, ?_⟩
  intro i hi
  exact wittPowerSeriesParameter_nonzero _ _ i hi

end SerrePositivity
