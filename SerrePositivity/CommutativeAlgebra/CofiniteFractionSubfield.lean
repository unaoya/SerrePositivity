module

public import SerrePositivity.CommutativeAlgebra.CofiniteFractionField
public import SerrePositivity.CommutativeAlgebra.PowerSeries.FractionField
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic

/-! # 共通分数体内の中間係数体族の実際の像

κ_e[[X]]→κ[[T]]、X_i↦T_i^pの分数体写像の像を部分体として構成する。
反単調性・下向きの有向性と、各部分体上の有限性・次数を確認する。
交わりの同定はCofiniteFractionIntersection.leanで行う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} (b : ι → K)

/-- 共通のFrac(κ[[T]])内で、中間係数体に沿う分数体写像の実際の像。 -/
def pBasisCofiniteFractionSubfield (e : Finset ι) :
    Subfield (FractionRing (MvPowerSeries σ K)) :=
  powerSeriesFractionSubfield (pBasisCofiniteField (p := p) b e) p (Fact.out : p.Prime).pos

/-- 各係数のp乗を、κ_eの元として取る実際の係数写像。 -/
def cofiniteFrobeniusCoefficientMap (e : Finset ι) :
    K →+* pBasisCofiniteField (p := p) b e :=
  (algebraMap (pPowerSubfield K p) (pBasisCofiniteField (p := p) b e)).comp
    (frobenius K p).rangeRestrictField

/-- 係数のp乗と変数のp乗を合わせると、共通分数体のFrobeniusになる。 -/
theorem cofiniteFractionMap_comp_frobeniusCoefficientMap (e : Finset ι) :
    (powerSeriesFractionMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
      (K := K) p (Fact.out : p.Prime).pos).comp
      (powerSeriesCoefficientFractionMap (cofiniteFrobeniusCoefficientMap b e)) =
      frobenius (FractionRing (MvPowerSeries σ K)) p := by
  apply IsFractionRing.ringHom_ext (A := MvPowerSeries σ K)
  intro f
  simp only [RingHom.comp_apply, powerSeriesCoefficientFractionMap_algebraMap,
    powerSeriesFractionMap_algebraMap, frobenius_def, ← map_pow]
  congr 1
  have hc : (algebraMap (pBasisCofiniteField (p := p) b e) K).comp
      (cofiniteFrobeniusCoefficientMap b e) = frobenius K p := by ext x; rfl
  change MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
      (MvPowerSeries.map (algebraMap (pBasisCofiniteField (p := p) b e) K)
        (MvPowerSeries.map (cofiniteFrobeniusCoefficientMap b e) f)) = f ^ p
  rw [MvPowerSeries.map_map, hc, ← MvPowerSeries.map_expand]
  exact MvPowerSeries.map_frobenius_expand p (Fact.out : p.Prime).ne_zero

/-- 共通分数体のp乗部分体は、各実際の像の部分体に含まれる。 -/
theorem pPowerSubfield_le_cofiniteFractionSubfield (e : Finset ι) :
    pPowerSubfield (FractionRing (MvPowerSeries σ K)) p ≤
      pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e := by
  rintro x ⟨a, rfl⟩
  refine ⟨powerSeriesCoefficientFractionMap (cofiniteFrobeniusCoefficientMap b e) a, ?_⟩
  exact congrArg (fun f ↦ f a) (cofiniteFractionMap_comp_frobeniusCoefficientMap b e)

/-- 全ての実際の像の交わりに、p乗部分体が含まれる。逆包含は交わりの別モジュールで証明する。 -/
theorem pPowerSubfield_le_iInf_cofiniteFractionSubfield :
    pPowerSubfield (FractionRing (MvPowerSeries σ K)) p ≤
      ⨅ e : Finset ι, pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e :=
  le_iInf (pPowerSubfield_le_cofiniteFractionSubfield b)

/-- 残す方向を増やすと、共通分数体内の像も小さくなる。 -/
theorem pBasisCofiniteFractionSubfield_antitone {e f : Finset ι} (hef : e ⊆ f) :
    pBasisCofiniteFractionSubfield (σ := σ) (p := p) b f ≤
      pBasisCofiniteFractionSubfield b e := by
  let φ := (IntermediateField.inclusion (pBasisCofiniteField_antitone (p := p) b hef)).toRingHom
  exact powerSeriesFractionSubfield_le_of_coefficientMap φ rfl p (Fact.out : p.Prime).pos

/-- 有限集合の和を使い、実際の像の部分体族は下向きに有向。 -/
theorem pBasisCofiniteFractionSubfield_directed :
    Directed (· ≥ ·) (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b) := by
  classical
  intro e f
  exact ⟨e ∪ f, pBasisCofiniteFractionSubfield_antitone b Finset.subset_union_left,
    pBasisCofiniteFractionSubfield_antitone b Finset.subset_union_right⟩

variable {b}

/-- 実際の像の部分体上でも、分数体の拡大次数はp^(h+|e|)。 -/
theorem IsPBasis.finrank_cofiniteFractionSubfield [Fintype σ]
    (hb : IsPBasis K p b) (e : Finset ι) :
    Module.finrank (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) = p ^ (Fintype.card σ + e.card) := by
  exact (finrank_fieldRange
    (powerSeriesFractionMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
      (K := K) p (Fact.out : p.Prime).pos)).trans (hb.finrank_cofiniteFractionField e)

/-- 各実際の像の部分体上で、共通分数体は有限次元。 -/
theorem IsPBasis.finite_cofiniteFractionSubfield [Finite σ]
    (hb : IsPBasis K p b) (e : Finset ι) :
    Module.Finite (pBasisCofiniteFractionSubfield (σ := σ) (p := p) b e)
      (FractionRing (MvPowerSeries σ K)) := by
  let : Fintype σ := Fintype.ofFinite σ
  apply Module.finite_of_finrank_pos
  rw [hb.finrank_cofiniteFractionSubfield e]
  exact pow_pos (Fact.out : p.Prime).pos _

end SerrePositivity
