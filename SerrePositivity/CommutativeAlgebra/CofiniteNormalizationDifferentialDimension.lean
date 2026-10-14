module

public import SerrePositivity.CommutativeAlgebra.CofiniteNormalizationDifferentialRank
public import SerrePositivity.CommutativeAlgebra.CofiniteFractionDifferentialBasis
public import SerrePositivity.CommutativeAlgebra.EqualCharacteristicNormalization
public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficientRestriction

/-! # 同じ有限正規化での完備微分の具体的な次元

共有限底体に沿う階数安定と、その底体上の微分基底の計算を合成する。
係数体の絶対p-rankの有限性や、分離的正規化の存在は仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι σ : Type*} [Finite σ] {b : ι → K}

/-- 通常有限正規化に対し、十分大きいfでκ_f上の完備微分の生成点の次元はh+|f|。 -/
theorem IsPBasis.exists_cofiniteNormalization_completed_finrank
    (hb : IsPBasis K p b)
    (F : MvPowerSeries σ K →+* D) (hF : Function.Injective F) (hfin : F.Finite)
    (hC : ∀ a, F (MvPowerSeries.C a) = algebraMap K D a)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, F (MvPowerSeries.X i) = z i)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b f) D)) =
        Nat.card σ + f.card := by
  let := Fintype.ofFinite σ
  obtain ⟨e, he⟩ := hb.exists_cofiniteNormalization_completed_rank_stable
    F hF hfin hC hres z hX hprimary
  refine ⟨e, ?_⟩
  intro f hf
  have h := (he f hf).trans (hb.finrank_cofiniteFractionDifferential (σ := σ) f)
  simpa only [Nat.card_eq_fintype_card] using h

/-- 係数写像とh個の準素パラメータから通常有限正規化を構成し、完備微分の次元を計算する。
分離的正規化の存在は入力に要求しない。 -/
theorem IsPBasis.exists_completed_finrank_of_parameters
    (hb : IsPBasis K p b) {h : ℕ} (hdim : ringKrullDim D = h)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : Fin h → D) (hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b f) D)) = h + f.card := by
  obtain ⟨F, hF, hfin, _, hC, hX⟩ := exists_injective_finite_powerSeries_map_of_parameters
    (algebraMap K D) hres hdim z hzm hprimary
  simpa only [Nat.card_fin] using
    hb.exists_cofiniteNormalization_completed_finrank F hF hfin hC hres z hX hprimary

/-- 準素パラメータから得た次元式は、有限集合fの外の像を保持する係数変更後も成立する。 -/
theorem IsPBasis.exists_completed_finrank_of_parameters_coefficientChange
    (hb : IsPBasis K p b) {h : ℕ} (hdim : ringKrullDim D = h)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : Fin h → D) (hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal D)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f → ∀ ψ : K →+* D,
      (∀ i, i ∉ f → algebraMap K D (b i) = ψ (b i)) →
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (cofiniteCoefficientDifferential (b := b) f ψ)) = h + f.card := by
  obtain ⟨e, he⟩ := hb.exists_completed_finrank_of_parameters hdim hres z hzm hprimary
  refine ⟨e, ?_⟩
  intro f hf ψ hagree
  have hold : Module.finrank (FractionRing D) (FractionRing D ⊗[D]
      AdicCompletion (IsLocalRing.maximalIdeal D)
        (cofiniteCoefficientDifferential (b := b) f (algebraMap K D))) = h + f.card := by
    have hA := congrArg (fun a : Algebra K D ↦
      letI : Algebra K D := a
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b f) D)))
      (toAlgebra_algebraMap (R := K) (S := D))
    exact hA.trans (he f hf)
  exact (hb.finrank_cofiniteCoefficientBaseChangeCompletedDifferential
    f (IsLocalRing.maximalIdeal D) (FractionRing D) (algebraMap K D) ψ hagree).symm.trans hold

end SerrePositivity
