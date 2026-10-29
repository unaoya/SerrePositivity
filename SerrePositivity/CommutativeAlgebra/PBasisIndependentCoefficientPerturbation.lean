module

public import SerrePositivity.CommutativeAlgebra.CofiniteCompletedDifferentialGeneration
public import SerrePositivity.CommutativeAlgebra.CofiniteNormalizationDifferentialDimension
public import SerrePositivity.CommutativeAlgebra.PBasisCoefficientPerturbation
public import SerrePositivity.RingTheory.Derivation

/-! # 微分が独立になる有限係数摂動

係数写像を型に保持した完備微分への絶対導分を使い、異なる係数作用を比較する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
open IsLocalRing

section ExplicitCoefficient
variable {K S L ι : Type*} [Field K] [CommRing S] [CommRing L] [Algebra S L]
  {p : ℕ} [Fact p.Prime] [CharP K p] {b : ι → K}

/-- 指定係数写像に沿う共有限完備微分への絶対導分。 -/
def cofiniteCoefficientBaseChangeCompletedDerivation (e : Finset ι) (I : Ideal S)
    (φ : K →+* S) :
    Derivation ℤ S (L ⊗[S] AdicCompletion I
      (cofiniteCoefficientDifferential (p := p) (b := b) e φ)) :=
  ((TensorProduct.mk S L _ 1).comp
    ((AdicCompletion.of I _).comp (cofiniteKaehlerRestriction (b := b) e φ))).compDer
      (KaehlerDifferential.D ℤ S)

@[simp] theorem cofiniteCoefficientBaseChangeCompletedDerivation_apply
    (e : Finset ι) (I : Ideal S) (φ : K →+* S) (s : S) :
    cofiniteCoefficientBaseChangeCompletedDerivation (L := L) (b := b) e I φ s =
      1 ⊗ₜ[S] AdicCompletion.of I _
        (cofiniteKaehlerRestriction (b := b) e φ (KaehlerDifferential.D ℤ S s)) := rfl

/-- 共通商による比較は指定係数の導分を保つ。 -/
@[simp] theorem IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_derivation
    (hb : IsPBasis K p b) (e : Finset ι) (I : Ideal S) (φ ψ : K →+* S)
    (hagree : ∀ i, i ∉ e → φ (b i) = ψ (b i)) (s : S) :
    hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv e I L φ ψ hagree
      (cofiniteCoefficientBaseChangeCompletedDerivation (L := L) (b := b) e I φ s) =
        cofiniteCoefficientBaseChangeCompletedDerivation (L := L) (b := b) e I ψ s :=
  hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_tmul_of
    e I L φ ψ hagree 1 (KaehlerDifferential.D ℤ S s)
end ExplicitCoefficient

section Selection
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}

/-- 通常の有限正規化の次元計算から、有限係数方向を独立にする極大イデアル内の元を選ぶ。 -/
theorem IsPBasis.exists_independent_coefficient_perturbation
    (hb : IsPBasis K p b) {h : ℕ} (hdim : ringKrullDim D = h)
    (hres : Function.Surjective ((residue D).comp (algebraMap K D)))
    (hm : maximalIdeal D ≠ ⊥)
    (z : Fin h → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ e : Finset ι, ∃ μ : e → D, (∀ i, μ i ∈ maximalIdeal D) ∧
      LinearIndependent (FractionRing D) (fun i : e ↦
        baseChangeCompletedKaehlerDerivation
          (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D)
            (algebraMap K D (b i) + μ i)) ∧
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b e) D)) = h + e.card := by
  classical
  obtain ⟨e, he⟩ := hb.exists_completed_finrank_of_parameters hdim hres z hzm hprimary
  let E := pBasisCofiniteField (p := p) b e
  let V := FractionRing D ⊗[D] AdicCompletion (maximalIdeal D) (KaehlerDifferential E D)
  let : Module.Finite (FractionRing D) V :=
    hb.moduleFinite_baseChange_completedKaehler_cofiniteField e hres
  let δ := baseChangeCompletedKaehlerDerivation (k := E) (FractionRing D) (maximalIdeal D)
  obtain ⟨μ, hμ, hi⟩ := exists_linearIndependent_derivation_perturbation
    δ (maximalIdeal D) hm (hb.span_range_baseChange_completedKaehler_cofiniteField e hres)
    (fun i : e ↦ δ (algebraMap K D (b i))) (by
      rw [he e (Finset.Subset.refl e), Fintype.card_coe]
      omega)
  exact ⟨e, μ, hμ, (by simpa only [map_add] using hi), he e (Finset.Subset.refl e)⟩
end Selection

section ResidueSection
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP D p] [CharP (ResidueField D) p]
  {ι : Type*} {b : ι → ResidueField D}

/-- 極大イデアルが非零なら、微分独立な有限係数方向を持つ新しい係数切断を構成する。 -/
theorem IsPBasis.exists_independent_coefficient_section
    (hb : IsPBasis (ResidueField D) p b)
    (φ : ResidueField D →+* D) (hφ : (residue D).comp φ = RingHom.id (ResidueField D))
    {h : ℕ} (hdim : ringKrullDim D = h) (hm : maximalIdeal D ≠ ⊥)
    (z : Fin h → D) (hzm : ∀ i, z i ∈ maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ (e : Finset ι) (ψ : ResidueField D →+* D),
      (residue D).comp ψ = RingHom.id (ResidueField D) ∧
      (∀ i, i ∉ e → φ (b i) = ψ (b i)) ∧
      LinearIndependent (FractionRing D) (fun i : e ↦
        cofiniteCoefficientBaseChangeCompletedDerivation (L := FractionRing D)
          (b := b) e (maximalIdeal D) ψ (ψ (b i))) ∧
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D) (cofiniteCoefficientDifferential (b := b) e ψ)) =
        h + e.card := by
  classical
  let : Algebra (ResidueField D) D := φ.toAlgebra
  have hres : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    change Function.Surjective ((residue D).comp φ)
    rw [hφ]
    exact Function.surjective_id
  obtain ⟨e, μ, hμ, hi, hdimold⟩ :=
    hb.exists_independent_coefficient_perturbation hdim hres hm z hzm hprimary
  let : IsAdicComplete (RingHom.ker (residue D)) D := by
    rw [ker_residue]
    infer_instance
  let ν : e → RingHom.ker (residue D) := fun i ↦ ⟨μ i, by simpa only [ker_residue] using hμ i⟩
  obtain ⟨ψ, hψ, hvalues, hagree⟩ := hb.exists_section_of_finitePerturbation
    (residue D) residue_surjective φ hφ e ν
  have heq : ∀ d : D,
      cofiniteCoefficientBaseChangeCompletedDerivation (L := FractionRing D)
        (b := b) e (maximalIdeal D) φ d =
      baseChangeCompletedKaehlerDerivation
        (k := pBasisCofiniteField (p := p) b e) (FractionRing D) (maximalIdeal D) d := by
    intro d
    simp only [cofiniteCoefficientBaseChangeCompletedDerivation_apply,
      baseChangeCompletedKaehlerDerivation_apply, cofiniteKaehlerRestriction_D]
  have hiold : LinearIndependent (FractionRing D) (fun i : e ↦
      cofiniteCoefficientBaseChangeCompletedDerivation (L := FractionRing D)
        (b := b) e (maximalIdeal D) φ (ψ (b i))) := by
    simpa only [heq, hvalues, ν, RingHom.algebraMap_toAlgebra] using hi
  have hagree' : ∀ i, i ∉ e → φ (b i) = ψ (b i) := fun i h ↦ (hagree i h).symm
  let q := hb.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv
    e (maximalIdeal D) (FractionRing D) φ ψ hagree'
  have hinew := hiold.map' q.toLinearMap q.ker
  refine ⟨e, ψ, hψ, hagree', ?_, ?_⟩
  · dsimp only [q] at hinew
    simpa only [Function.comp_def, LinearEquiv.coe_coe,
      IsPBasis.cofiniteCoefficientBaseChangeCompletedDifferentialEquiv_derivation] using hinew
  · exact q.finrank_eq.symm.trans hdimold
end ResidueSection

end SerrePositivity
