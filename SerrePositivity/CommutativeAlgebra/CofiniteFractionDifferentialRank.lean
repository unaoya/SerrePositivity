module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionDifferential
public import SerrePositivity.FieldTheory.SubfieldFamilyDifferentialRank

/-! # 実際の共有限分数体族に対する有限拡大一般での階数安定

有限変数の冪級数の分数体K₀と、その任意の有限拡大Lについて、
実際の族F_eの性質を確認して一般定理を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ ι L : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  [Finite σ] {b : ι → K} [Field L]
  [Algebra (FractionRing (MvPowerSeries σ K)) L] [CharP L p]
  [Module.Finite (FractionRing (MvPowerSeries σ K)) L]

/-- 任意の有限拡大で、十分小さい実際の部分体と、その下の共有限底体で通常微分の次元が等しい。 -/
theorem IsPBasis.exists_cofiniteFractionSubfield_rank_stable (hb : IsPBasis K p b) :
    ∃ e : Finset ι, ∀ R : Subfield (FractionRing (MvPowerSeries σ K)),
      Module.Finite R (FractionRing (MvPowerSeries σ K)) →
      R ≤ pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e →
      letI : Algebra R L :=
        ((algebraMap (FractionRing (MvPowerSeries σ K)) L).comp
          (algebraMap R (FractionRing (MvPowerSeries σ K)))).toAlgebra
      letI : Module R L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R L)
      letI : SMul R L := (inferInstance : Algebra R L).toSMul
      Module.finrank L (KaehlerDifferential R L) =
        Module.finrank (FractionRing (MvPowerSeries σ K))
          (KaehlerDifferential R (FractionRing (MvPowerSeries σ K))) := by
  exact exists_subfieldFamily_rank_stable
    (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b) hb.finite_cofiniteFractionSubfield
    (pBasisCofiniteFractionSubfield_directed b)
    (pPowerSubfield_le_cofiniteFractionSubfield b) hb.iInf_cofiniteFractionSubfield_eq_pPower

/-- 十分大きい有限集合以降の実際の族で、有限拡大前後の通常微分の次元が等しい。 -/
theorem IsPBasis.exists_cofiniteFractionSubfield_rank_stable_of_superset
    (hb : IsPBasis K p b) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      letI : Algebra (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f) L :=
        ((algebraMap (FractionRing (MvPowerSeries σ K)) L).comp
          (algebraMap (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f)
            (FractionRing (MvPowerSeries σ K)))).toAlgebra
      letI : Module (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f) L :=
        @Algebra.toModule _ _ _ _ (inferInstance :
          Algebra (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f) L)
      letI : SMul (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f) L :=
        (inferInstance : Algebra (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f) L).toSMul
      Module.finrank L (KaehlerDifferential
        (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f) L) =
        Module.finrank (FractionRing (MvPowerSeries σ K)) (KaehlerDifferential
          (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f)
          (FractionRing (MvPowerSeries σ K))) := by
  obtain ⟨e, he⟩ := hb.exists_cofiniteFractionSubfield_rank_stable (σ := σ) (L := L)
  refine ⟨e, ?_⟩
  intro f hf
  exact he (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f)
    (hb.finite_cofiniteFractionSubfield f) (pBasisCofiniteFractionSubfield_antitone b hf)

/-- 実際の像の部分体を与える分数体そのものを底体として、同じ作用で階数安定を適用する。 -/
theorem IsPBasis.exists_cofiniteFractionField_rank_stable (hb : IsPBasis K p b) :
    ∃ e : Finset ι, ∀ f : Finset ι, e ⊆ f →
      letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
      letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) := powerSeriesFractionModule p (Fact.out : p.Prime).pos
      letI : SMul (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K)) :=
        (inferInstance : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K))).toSMul
      letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L :=
        ((algebraMap (FractionRing (MvPowerSeries σ K)) L).comp
          (powerSeriesFractionMap p (Fact.out : p.Prime).pos)).toAlgebra
      letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L :=
        @Algebra.toModule _ _ _ _ (inferInstance :
          Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L)
      letI : SMul (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L :=
        (inferInstance : Algebra
          (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L).toSMul
      Module.finrank L (KaehlerDifferential
        (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))) L) =
        Module.finrank (FractionRing (MvPowerSeries σ K)) (KaehlerDifferential
          (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f)))
          (FractionRing (MvPowerSeries σ K))) := by
  let := Fintype.ofFinite σ
  obtain ⟨e, he⟩ := exists_subfieldFamily_rank_stable_of_finite
    (K := FractionRing (MvPowerSeries σ K)) (L := L)
    (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b) hb.finite_cofiniteFractionSubfield
    (pBasisCofiniteFractionSubfield_directed b)
    (pPowerSubfield_le_cofiniteFractionSubfield b) hb.iInf_cofiniteFractionSubfield_eq_pPower
  refine ⟨e, ?_⟩
  intro f hf
  let Q := FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b f))
  let K₀ := FractionRing (MvPowerSeries σ K)
  let : Algebra Q K₀ := (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module Q K₀ := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  let : SMul Q K₀ := (inferInstance : Algebra Q K₀).toSMul
  let : Algebra Q L := ((algebraMap K₀ L).comp
    (powerSeriesFractionMap p (Fact.out : p.Prime).pos)).toAlgebra
  let : Module Q L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra Q L)
  let : SMul Q L := (inferInstance : Algebra Q L).toSMul
  let : IsScalarTower Q K₀ L := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite Q K₀ := Module.Finite.of_basis (hb.cofiniteFractionBasis (σ := σ) f)
  apply he Q
  rintro _ ⟨q, rfl⟩
  exact pBasisCofiniteFractionSubfield_antitone b hf ⟨q, rfl⟩

end SerrePositivity
