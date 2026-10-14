module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionIntersection

/-! # 同じ有限正規化の分数体内へ中間体族を移す

指定した有限単射Fを延長し、κ_e[[X]]の実際の像をFrac(D)内に構成する。
交わりは埋め込んだFrac(κ[[T]])のp乗部分体の像である。
Frac(D)全体のp乗部分体との一致や、分離性は主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ D ι : Type*} [Field K] [CommRing D] [IsDomain D]
  {p : ℕ} [Fact p.Prime] [CharP K p] (b : ι → K)
  (F : MvPowerSeries σ K →+* D) (hF : Function.Injective F)

/-- 指定した正規化の同じ分数体写像を通して得る実際の部分体族。 -/
def pBasisNormalizationFractionSubfield (e : Finset ι) : Subfield (FractionRing D) :=
  (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e).map (fractionRingMap F hF)

/-- 移送した部分体は、FとX_i↦T_i^pの合成を延長した写像の像そのもの。 -/
theorem pBasisNormalizationFractionSubfield_eq_fieldRange (e : Finset ι) :
    pBasisNormalizationFractionSubfield (p := p) b F hF e =
      (fractionRingMap
        (F.comp (powerSeriesExpandMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
          (K := K) p (Fact.out : p.Prime).pos))
        (hF.comp (powerSeriesExpandMap_injective p (Fact.out : p.Prime).pos
          (RingHom.injective _)))).fieldRange := by
  rw [fractionRingMap_comp]
  exact RingHom.map_fieldRange _ _

/-- 反単調性は同じ埋め込みを通して保存される。 -/
theorem pBasisNormalizationFractionSubfield_antitone {e f : Finset ι} (hef : e ⊆ f) :
    pBasisNormalizationFractionSubfield (p := p) b F hF f ≤
      pBasisNormalizationFractionSubfield (p := p) b F hF e :=
  (Subfield.gc_map_comap (fractionRingMap F hF)).monotone_l
    (pBasisCofiniteFractionSubfield_antitone b hef)

/-- 同じ埋め込みを通して移した族も下向きに有向。 -/
theorem pBasisNormalizationFractionSubfield_directed :
    Directed (· ≥ ·) (pBasisNormalizationFractionSubfield (p := p) b F hF) := by
  classical
  intro e f
  exact ⟨e ∪ f,
    pBasisNormalizationFractionSubfield_antitone b F hF Finset.subset_union_left,
    pBasisNormalizationFractionSubfield_antitone b F hF Finset.subset_union_right⟩

variable {b}

/-- Frac(D)内での交わりは、元の共通分数体のp乗部分体をFで移した像。 -/
theorem IsPBasis.iInf_normalizationFractionSubfield_eq_map_pPower [Finite σ]
    (hb : IsPBasis K p b) :
    (⨅ e : Finset ι, pBasisNormalizationFractionSubfield (p := p) b F hF e) =
      (pPowerSubfield (FractionRing (MvPowerSeries σ K)) p).map (fractionRingMap F hF) := by
  rw [← hb.iInf_cofiniteFractionSubfield_eq_pPower]
  exact (Subfield.map_iInf (fractionRingMap F hF) _).symm

/-- 有限正規化Fに対して、Frac(D)は各実際の像の部分体上で有限次元。 -/
theorem IsPBasis.finite_normalizationFractionSubfield [Finite σ]
    (hb : IsPBasis K p b) (hfin : F.Finite) (e : Finset ι) :
    Module.Finite (pBasisNormalizationFractionSubfield (p := p) b F hF e)
      (FractionRing D) := by
  rw [pBasisNormalizationFractionSubfield_eq_fieldRange]
  exact fractionRingMap_fieldRange_finite _ _
    (hfin.comp (hb.powerSeries_cofinite_expand_injective_finite e).2)

end SerrePositivity
