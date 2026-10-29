module

public import SerrePositivity.CommutativeAlgebra.PBasisIndependentCoefficientPerturbation
public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficient
public import Mathlib.RingTheory.Localization.Module

/-! # Cohen–Gabberの係数体変更による次元減少

共有限係数体上の独立な係数方向を消し、全係数体上の完備微分の次元を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
open IsLocalRing

section Dimension
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}

/-- 独立な有限係数方向を消すと、全係数体上の完備微分の次元はhとなる。 -/
theorem IsPBasis.finrank_completedKaehler_of_independent_coefficient_directions
    (hb : IsPBasis K p b) (e : Finset ι) {h : ℕ}
    (hres : Function.Surjective ((residue D).comp (algebraMap K D)))
    (hi : LinearIndependent (FractionRing D) (fun i : e ↦
      baseChangeCompletedKaehlerDerivation
        (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D)
          (algebraMap K D (b i))))
    (hdim : Module.finrank (FractionRing D) (FractionRing D ⊗[D]
      AdicCompletion (maximalIdeal D)
        (KaehlerDifferential (pBasisCofiniteField (p := p) b e) D)) = h + e.card) :
    Module.finrank (FractionRing D) (FractionRing D ⊗[D]
      AdicCompletion (maximalIdeal D) (KaehlerDifferential K D)) = h := by
  classical
  let E := pBasisCofiniteField (p := p) b e
  let C := AdicCompletion (maximalIdeal D) (KaehlerDifferential E D)
  let : Module.Finite D C := hb.moduleFinite_completedKaehler_cofiniteField e hres
    (maximalIdeal D) (maximalIdeal.isMaximal D).isPrime.radical
  let g : C →ₗ[D] AdicCompletion (maximalIdeal D) (KaehlerDifferential K D) :=
    (AdicCompletion.map (maximalIdeal D) (KaehlerDifferential.map E K D D)).restrictScalars D
  have hg : Function.Surjective g :=
    AdicCompletion.map_surjective (maximalIdeal D) (KaehlerDifferential.map_surjective E K D)
  let f := g.baseChange (FractionRing D)
  have hf : Function.Surjective f := LinearMap.baseChange_surjective (FractionRing D) hg
  have hker : LinearMap.ker f = Submodule.span (FractionRing D) (Set.range (fun i : e ↦
      baseChangeCompletedKaehlerDerivation (k := E) (FractionRing D) (maximalIdeal D)
        (algebraMap K D (b i)))) :=
    ker_baseChange_eq_span_of_ker_eq_span (FractionRing D) g _
      (hb.ker_completed_cofiniteToFullKaehlerRestriction e (maximalIdeal D)
        (maximalIdeal_le_jacobson ⊥))
  have hkdim : Module.finrank (FractionRing D) (LinearMap.ker f) = e.card := by
    rw [hker, finrank_span_eq_card hi, Fintype.card_coe]
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hkdim] at h
  rw [hdim] at h
  omega
end Dimension

section Existence
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP D p] [CharP (ResidueField D) p]
  {ι : Type*} {b : ι → ResidueField D}

/-- 係数切断を変更し、全係数体上の完備微分の生成点の次元を環の次元へ減らす。 -/
theorem IsPBasis.exists_coefficient_section_completed_finrank
    (hb : IsPBasis (ResidueField D) p b)
    (φ : ResidueField D →+* D) (hφ : (residue D).comp φ = RingHom.id (ResidueField D))
    {h : ℕ} (hdim : ringKrullDim D = h) (hm : maximalIdeal D ≠ ⊥)
    (z : Fin h → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ ψ : ResidueField D →+* D,
      (residue D).comp ψ = RingHom.id (ResidueField D) ∧
      letI : Algebra (ResidueField D) D := ψ.toAlgebra
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D) (KaehlerDifferential (ResidueField D) D)) = h := by
  obtain ⟨e, ψ, hψ, _, hi, hdimψ⟩ :=
    hb.exists_independent_coefficient_section φ hφ hdim hm z hzm hprimary
  refine ⟨ψ, hψ, ?_⟩
  let : Algebra (ResidueField D) D := ψ.toAlgebra
  have hres : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    change Function.Surjective ((residue D).comp ψ)
    rw [hψ]
    exact Function.surjective_id
  have hi' : LinearIndependent (FractionRing D) (fun i : e ↦
      baseChangeCompletedKaehlerDerivation
        (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D)
          (algebraMap (ResidueField D) D (b i))) := by
    simpa only [cofiniteCoefficientBaseChangeCompletedDerivation_apply,
      cofiniteKaehlerRestriction_D, baseChangeCompletedKaehlerDerivation_apply,
      RingHom.algebraMap_toAlgebra] using hi
  exact hb.finrank_completedKaehler_of_independent_coefficient_directions e hres hi' hdimψ
end Existence

end SerrePositivity
