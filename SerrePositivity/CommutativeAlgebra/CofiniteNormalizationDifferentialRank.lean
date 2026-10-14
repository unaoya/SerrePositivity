module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionDifferentialRank
public import SerrePositivity.CommutativeAlgebra.CofiniteCompletedDifferentialComparison

/-! # 同じ有限正規化における完備微分の階数安定

κ[[T]]→Dを固定し、κ_f[[X]]→DをX_i↦z_i^pとして構成する。
分数体上の通常微分の階数安定と、極大イデアル進の完備微分の比較を
同じ底体写像で接続する。具体的な次元h+|f|の計算はここでは主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
variable {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
  [IsNoetherianRing D] [IsLocalRing D]
  [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP K p] {ι σ : Type*} [Finite σ] {b : ι → K}

/-- 通常有限正規化を固定すると、十分大きい有限集合以降で完備微分の階数が
元の冪級数分数体の相対微分の階数に一致する。 -/
theorem IsPBasis.exists_cofiniteNormalization_completed_rank_stable
    (hb : IsPBasis K p b)
    (F : MvPowerSeries σ K →+* D) (hF : Function.Injective F) (hfin : F.Finite)
    (hC : ∀ a, F (MvPowerSeries.C a) = algebraMap K D a)
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap K D)))
    (z : σ → D) (hX : ∀ i, F (MvPowerSeries.X i) = z i)
    (hprimary : (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
      letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        powerSeriesFractionModule p (Fact.out : p.Prime).pos
      letI : SMul (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (inferInstance : Algebra
          (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K))).toSMul
      Module.finrank (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (IsLocalRing.maximalIdeal D)
          (KaehlerDifferential (pBasisCofiniteField (p := p) b f) D)) =
      Module.finrank (FractionRing (MvPowerSeries σ K)) (KaehlerDifferential
        (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
        (FractionRing (MvPowerSeries σ K))) := by
  let K₀ := FractionRing (MvPowerSeries σ K)
  let L := FractionRing D
  let : Algebra K₀ L := (fractionRingMap F hF).toAlgebra
  let : Module K₀ L := fractionRingMapModule F hF
  let : SMul K₀ L := (inferInstance : Algebra K₀ L).toSMul
  let : Module.Finite K₀ L := fractionRingMap_finite F hF hfin
  let : CharP D p := charP_of_injective_algebraMap (algebraMap K D).injective p
  let : CharP L p := charP_of_injective_algebraMap (IsFractionRing.injective D L) p
  obtain ⟨e, he⟩ := hb.exists_cofiniteFractionField_rank_stable (σ := σ) (L := L)
  refine ⟨e, ?_⟩
  intro f hf
  let E := pBasisCofiniteField (p := p) b f
  let A := MvPowerSeries σ E
  let Q := FractionRing A
  let ψ : A →+* MvPowerSeries σ K := powerSeriesExpandMap p (Fact.out : p.Prime).pos
  let φ : Q →+* K₀ := powerSeriesFractionMap p (Fact.out : p.Prime).pos
  let : Algebra Q K₀ := φ.toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  let : Algebra Q L := ((algebraMap K₀ L).comp φ).toAlgebra
  let : Module Q L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra Q L)
  let : SMul Q L := (inferInstance : Algebra Q L).toSMul
  let : Algebra A D := (F.comp ψ).toAlgebra
  let : Module A D := @Algebra.toModule _ _ _ _ (inferInstance : Algebra A D)
  let : SMul A D := (inferInstance : Algebra A D).toSMul
  let : Module.Finite A D := hfin.comp (hb.powerSeries_cofinite_expand_injective_finite f).2
  let : IsScalarTower E A D := IsScalarTower.of_algebraMap_eq (fun a ↦ by
    change algebraMap E D a = F (ψ (MvPowerSeries.C a))
    rw [powerSeriesExpandMap_C, hC]
    exact IsScalarTower.algebraMap_apply E K D a)
  have hXp : ∀ i, algebraMap A D (MvPowerSeries.X i) = z i ^ p := by
    intro i
    change F (ψ (MvPowerSeries.X i)) = z i ^ p
    rw [powerSeriesExpandMap_X, map_pow, hX]
  let : Algebra A L := ((algebraMap D L).comp (F.comp ψ)).toAlgebra
  let : Module A L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra A L)
  let : SMul A L := (inferInstance : Algebra A L).toSMul
  let : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A Q L := IsScalarTower.of_algebraMap_eq (fun a ↦ by
    change algebraMap D L (F (ψ a)) = fractionRingMap F hF
      (powerSeriesFractionMap p (Fact.out : p.Prime).pos (algebraMap A Q a))
    rw [powerSeriesFractionMap_algebraMap, fractionRingMap_algebraMap])
  exact (hb.finrank_cofiniteMaximalCompletedFractionDifferential
    f Q L hres z hXp hprimary).trans (he f hf)

end SerrePositivity
