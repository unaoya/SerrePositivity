module

public import SerrePositivity.CommutativeAlgebra.CohenGabberCoefficientField
public import SerrePositivity.CommutativeAlgebra.DifferentialParameterSelection

/-! # Cohen–Gabberの微分パラメータ

通常有限正規化から非零パラメータを得て、係数切断を変更し、微分基底を持つパラメータを選ぶ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open IsLocalRing
open scoped TensorProduct

/-- 単射な冪級数評価の変数の像は非零。 -/
theorem powerSeries_variable_image_ne_zero
    {k D σ : Type*} [CommRing k] [Nontrivial k] [CommRing D]
    (F : MvPowerSeries σ k →+* D) (hF : Function.Injective F) (i : σ) :
    F (MvPowerSeries.X i) ≠ 0 := by
  intro hz
  have hX : (MvPowerSeries.X i : MvPowerSeries σ k) = 0 := hF (hz.trans F.map_zero.symm)
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) hX
  exact one_ne_zero (by
    simpa only [MvPowerSeries.coeff_index_single_self_X, map_zero] using h)

/-- 非零極大イデアルの完備局所整域では、係数切断と微分基底を持つパラメータを同時に選べる。 -/
theorem exists_coefficient_section_differential_parameters
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] (hm : maximalIdeal D ≠ ⊥) :
    ∃ (ψ : ResidueField D →+* D) (y : Fin h → D),
      (residue D).comp ψ = RingHom.id (ResidueField D) ∧
      (∀ i, y i ∈ maximalIdeal D) ∧
      (Ideal.span (Set.range y)).radical = maximalIdeal D ∧
      letI : Algebra (ResidueField D) D := ψ.toAlgebra
      ∃ B : Module.Basis (Fin h) (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D) (KaehlerDifferential (ResidueField D) D)),
        ∀ i, B i = baseChangeCompletedKaehlerDerivation
          (k := ResidueField D) (FractionRing D) (maximalIdeal D) (y i) := by
  classical
  let : CharP (ResidueField D) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (residue D), CharP.cast_eq_zero, map_zero])
  obtain ⟨φ, τ, F, hφ, hτ, hF, _, _, _, hFX⟩ :=
    exists_equalCharacteristic_finite_normalization D hdim p
  have hτm : ∀ i, τ i ∈ maximalIdeal D := by
    intro i
    rw [← hτ.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  obtain ⟨s, hs⟩ := exists_pBasis (K := ResidueField D) (p := p)
  obtain ⟨ψ, hψ, hdimψ⟩ := hs.exists_coefficient_section_completed_finrank
    φ hφ hdim hm τ hτm hτ.2
  let : Algebra (ResidueField D) D := ψ.toAlgebra
  have hres : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    change Function.Surjective ((residue D).comp ψ)
    rw [hψ]
    exact Function.surjective_id
  let : Module.Finite D (AdicCompletion (maximalIdeal D)
      (KaehlerDifferential (ResidueField D) D)) :=
    moduleFinite_completedKaehler_of_primary_common_residue hres (maximalIdeal D)
      (maximalIdeal.isMaximal D).isPrime.radical
  have hτ0 : ∀ i, τ i ≠ 0 := fun i ↦ hFX i ▸ powerSeries_variable_image_ne_zero F hF i
  obtain ⟨y, B, hym, hyprim, hB⟩ := exists_parameters_with_derivation_basis p
    (baseChangeCompletedKaehlerDerivation (k := ResidueField D)
      (FractionRing D) (maximalIdeal D)) hm
    (span_range_baseChangeCompletedKaehlerDerivation_eq_top
      (FractionRing D) (maximalIdeal D) (maximalIdeal_le_jacobson ⊥))
    hdimψ τ hτm hτ0 hτ.2
  exact ⟨ψ, y, hψ, hym, hyprim, B, hB⟩

end SerrePositivity
