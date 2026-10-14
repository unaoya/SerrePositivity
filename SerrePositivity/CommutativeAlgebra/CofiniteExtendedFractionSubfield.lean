module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionIntersection
public import SerrePositivity.FieldTheory.PrimeRootPowerSubfield
public import SerrePositivity.FieldTheory.SubfieldFiniteExtension
public import SerrePositivity.FieldTheory.SubfieldFamilyPrimeRootRank
public import SerrePositivity.FieldTheory.SeparablePowerSubfieldIntersection
public import SerrePositivity.FieldTheory.SubfieldFamilyTower
public import SerrePositivity.FieldTheory.FiniteExtensionPowerSubfieldIntersection

/-! # 分数体の拡大後の共有限部分体族

K₀=Frac(κ[[T]])の族F_eをLへ写し、L^pを添加した族G_e=F_e(L^p)を構成する。
共有限性と下向き有向性は任意の有限拡大で保存される。
交わりがL^pとなることを有限拡大一般で証明し、次の次数pの階数安定へ再適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ ι L : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  (b : ι → K) [Field L]
  [Algebra (FractionRing (MvPowerSeries σ K)) L] [CharP L p]

/-- 拡大後のp乗部分体を添加した、実際の共有限部分体族。 -/
def pBasisExtendedFractionSubfield (e : Finset ι) : Subfield L :=
  (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e).map
    (algebraMap (FractionRing (MvPowerSeries σ K)) L) ⊔ pPowerSubfield L p

/-- 定義により、各底体は拡大後のp乗部分体を含む。 -/
theorem pPowerSubfield_le_extendedFractionSubfield (e : Finset ι) :
    pPowerSubfield L p ≤ pBasisExtendedFractionSubfield (σ := σ) (L := L) b e :=
  le_sup_right

/-- 有限集合を大きくすると、拡大後も底体は小さくなる。 -/
theorem pBasisExtendedFractionSubfield_antitone {e f : Finset ι} (hef : e ⊆ f) :
    pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b f ≤
      pBasisExtendedFractionSubfield (σ := σ) (L := L) b e := by
  apply sup_le_sup_right
  exact (Subfield.gc_map_comap (algebraMap (FractionRing (MvPowerSeries σ K)) L)).monotone_l
    (pBasisCofiniteFractionSubfield_antitone b hef)

/-- 拡大後の族も有限集合の和で下向きに有向。 -/
theorem pBasisExtendedFractionSubfield_directed :
    Directed (· ≥ ·) (pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b) := by
  classical
  intro e f
  exact ⟨e ∪ f, pBasisExtendedFractionSubfield_antitone b Finset.subset_union_left,
    pBasisExtendedFractionSubfield_antitone b Finset.subset_union_right⟩

variable {b} [Finite σ]

/-- 元の族の共有限性とL/K₀の有限性を確認すると、拡大後も各底体は共有限。 -/
theorem IsPBasis.finite_extendedFractionSubfield
    [Module.Finite (FractionRing (MvPowerSeries σ K)) L]
    (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Finite (pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e) L := by
  let : Module.Finite (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) := hb.finite_cofiniteFractionSubfield e
  exact finite_subfield_sup_pPower (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)

/-- p乗根で生成された実際の拡大について、有限性も生成条件から供給する。 -/
theorem IsPBasis.finite_extendedFractionSubfield_of_primeRoot
    (hb : IsPBasis K p b) (x : L) (a : FractionRing (MvPowerSeries σ K))
    (hpow : x ^ p = algebraMap (FractionRing (MvPowerSeries σ K)) L a)
    (hs : Algebra.adjoin (FractionRing (MvPowerSeries σ K)) {x} = ⊤) (e : Finset ι) :
    Module.Finite (pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e) L := by
  let B := PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a hpow) hs
  let : Module.Finite (FractionRing (MvPowerSeries σ K)) L := B.finite
  exact hb.finite_extendedFractionSubfield e

/-- 非自明な次数pの拡大では、実際の拡大後の族の交わりはL^p。
微分の非零性や交わりの結論を仮定として渡さず、元の族で確認して適用する。 -/
theorem IsPBasis.iInf_extendedFractionSubfield_primeRoot_eq_pPower
    (hb : IsPBasis K p b) (x : L) (a : FractionRing (MvPowerSeries σ K))
    (hpow : x ^ p = algebraMap (FractionRing (MvPowerSeries σ K)) L a)
    (hx : x ∉ Set.range (algebraMap (FractionRing (MvPowerSeries σ K)) L))
    (hs : Algebra.adjoin (FractionRing (MvPowerSeries σ K)) {x} = ⊤) :
    (⨅ e : Finset ι, pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e) =
      pPowerSubfield L p := by
  exact iInf_subfield_sup_pPower_primeRoot
    (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b)
    (pBasisCofiniteFractionSubfield_directed b)
    (pPowerSubfield_le_cofiniteFractionSubfield b)
    hb.iInf_cofiniteFractionSubfield_eq_pPower x a hpow hx hs

/-- 実際の拡大後の族へ共通の階数安定定理を再適用する。
二段目の次数pの添加に必要な有限性・p乗部分体の包含・交わりを一段目から供給する。 -/
theorem IsPBasis.exists_extendedFractionSubfield_primeRoot_rank_stable
    {M : Type*} [Field M] [Algebra L M] [CharP M p]
    (hb : IsPBasis K p b) (x : L) (a : FractionRing (MvPowerSeries σ K))
    (hpow : x ^ p = algebraMap (FractionRing (MvPowerSeries σ K)) L a)
    (hx : x ∉ Set.range (algebraMap (FractionRing (MvPowerSeries σ K)) L))
    (hs : Algebra.adjoin (FractionRing (MvPowerSeries σ K)) {x} = ⊤)
    (y : M) (c : L) (hpow' : y ^ p = algebraMap L M c)
    (hy : y ∉ Set.range (algebraMap L M)) (hs' : Algebra.adjoin L {y} = ⊤) :
    ∃ e : Finset ι, ∀ R : Subfield L, Module.Finite R L →
      R ≤ pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e →
      letI : Algebra R M := ((algebraMap L M).comp (algebraMap R L)).toAlgebra
      letI : Module R M := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R M)
      letI : SMul R M := (inferInstance : Algebra R M).toSMul
      Module.finrank M (KaehlerDifferential R M) = Module.finrank L (KaehlerDifferential R L) := by
  exact exists_subfieldFamily_primeRoot_rank_stable
    (pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b)
    (hb.finite_extendedFractionSubfield_of_primeRoot x a hpow hs)
    (pPowerSubfield_le_extendedFractionSubfield b)
    (hb.iInf_extendedFractionSubfield_primeRoot_eq_pPower x a hpow hx hs)
    y c hpow' hy hs'

/-- 分離的有限拡大でも、実際の拡大後の族の交わりはL^p。 -/
theorem IsPBasis.iInf_extendedFractionSubfield_of_isSeparable
    [Module.Finite (FractionRing (MvPowerSeries σ K)) L]
    [Algebra.IsSeparable (FractionRing (MvPowerSeries σ K)) L]
    (hb : IsPBasis K p b) :
    (⨅ e : Finset ι, pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e) =
      pPowerSubfield L p := by
  exact iInf_subfield_sup_pPower_of_isSeparable
    (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b)
    hb.finite_cofiniteFractionSubfield (pBasisCofiniteFractionSubfield_directed b)
    (pPowerSubfield_le_cofiniteFractionSubfield b) hb.iInf_cofiniteFractionSubfield_eq_pPower

/-- 分離的有限拡大の後にも、次の次数pの階数安定定理を実際の族へ再適用できる。 -/
theorem IsPBasis.exists_extendedFractionSubfield_primeRoot_rank_stable_of_isSeparable
    [Module.Finite (FractionRing (MvPowerSeries σ K)) L]
    [Algebra.IsSeparable (FractionRing (MvPowerSeries σ K)) L]
    {M : Type*} [Field M] [Algebra L M] [CharP M p]
    (hb : IsPBasis K p b) (y : M) (c : L) (hpow : y ^ p = algebraMap L M c)
    (hy : y ∉ Set.range (algebraMap L M)) (hs : Algebra.adjoin L {y} = ⊤) :
    ∃ e : Finset ι, ∀ R : Subfield L, Module.Finite R L →
      R ≤ pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e →
      letI : Algebra R M := ((algebraMap L M).comp (algebraMap R L)).toAlgebra
      letI : Module R M := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R M)
      letI : SMul R M := (inferInstance : Algebra R M).toSMul
      Module.finrank M (KaehlerDifferential R M) = Module.finrank L (KaehlerDifferential R L) := by
  exact exists_subfieldFamily_primeRoot_rank_stable
    (pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b)
    hb.finite_extendedFractionSubfield (pPowerSubfield_le_extendedFractionSubfield b)
    hb.iInf_extendedFractionSubfield_of_isSeparable y c hpow hy hs

omit [Finite σ] in
/-- 実際の族を二つの拡大に沿って構成しても、合成した拡大での族と同じ部分体になる。 -/
theorem pBasisExtendedFractionSubfield_tower
    {M : Type*} [Field M] [Algebra L M] [CharP M p]
    [Algebra (FractionRing (MvPowerSeries σ K)) M]
    [IsScalarTower (FractionRing (MvPowerSeries σ K)) L M]
    (e : Finset ι) :
    (pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e).map (algebraMap L M) ⊔
        pPowerSubfield M p =
      pBasisExtendedFractionSubfield (σ := σ) (L := M) (p := p) b e :=
  map_subfield_sup_pPower_tower (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)

/-- 有限拡大一般で、実際の拡大後の族の交わりはL^p。 -/
theorem IsPBasis.iInf_extendedFractionSubfield_of_finite
    [Module.Finite (FractionRing (MvPowerSeries σ K)) L]
    (hb : IsPBasis K p b) :
    (⨅ e : Finset ι, pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e) =
      pPowerSubfield L p := by
  exact iInf_subfield_sup_pPower_of_finite
    (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b) hb.finite_cofiniteFractionSubfield
    (pBasisCofiniteFractionSubfield_directed b)
    (pPowerSubfield_le_cofiniteFractionSubfield b) hb.iInf_cofiniteFractionSubfield_eq_pPower

/-- 任意の有限拡大の後にも、実際の族で次の次数pの階数安定定理を使える。 -/
theorem IsPBasis.exists_extendedFractionSubfield_primeRoot_rank_stable_of_finite
    [Module.Finite (FractionRing (MvPowerSeries σ K)) L]
    {M : Type*} [Field M] [Algebra L M] [CharP M p]
    (hb : IsPBasis K p b) (y : M) (c : L) (hpow : y ^ p = algebraMap L M c)
    (hy : y ∉ Set.range (algebraMap L M)) (hs : Algebra.adjoin L {y} = ⊤) :
    ∃ e : Finset ι, ∀ R : Subfield L, Module.Finite R L →
      R ≤ pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b e →
      letI : Algebra R M := ((algebraMap L M).comp (algebraMap R L)).toAlgebra
      letI : Module R M := @Algebra.toModule _ _ _ _ (inferInstance : Algebra R M)
      letI : SMul R M := (inferInstance : Algebra R M).toSMul
      Module.finrank M (KaehlerDifferential R M) = Module.finrank L (KaehlerDifferential R L) := by
  exact exists_subfieldFamily_primeRoot_rank_stable
    (pBasisExtendedFractionSubfield (σ := σ) (L := L) (p := p) b)
    hb.finite_extendedFractionSubfield (pPowerSubfield_le_extendedFractionSubfield b)
    hb.iInf_extendedFractionSubfield_of_finite y c hpow hy hs

end SerrePositivity
