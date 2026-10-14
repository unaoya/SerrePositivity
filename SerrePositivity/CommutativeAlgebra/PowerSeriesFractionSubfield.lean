module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesFractionField
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # 係数写像と分数体内の実際の像

係数の包含を、同じ変数のq乗による写像の合成へ移す。
分数体の写像の一意性から、その像の部分体の包含を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {E F K σ : Type*} [Field E] [Field F] [Field K]

/-- 係数写像だけを作用させ、変数を保つ分数体の写像。 -/
def powerSeriesCoefficientFractionMap (φ : E →+* F) :
    FractionRing (MvPowerSeries σ E) →+* FractionRing (MvPowerSeries σ F) :=
  fractionRingMap (MvPowerSeries.map φ) (by
    intro f g hfg
    ext d
    apply φ.injective
    simpa only [MvPowerSeries.coeff_map] using congrArg (MvPowerSeries.coeff d) hfg)

@[simp] theorem powerSeriesCoefficientFractionMap_algebraMap (φ : E →+* F)
    (f : MvPowerSeries σ E) :
    powerSeriesCoefficientFractionMap φ (algebraMap _ (FractionRing (MvPowerSeries σ E)) f) =
      algebraMap _ (FractionRing (MvPowerSeries σ F)) (MvPowerSeries.map φ f) :=
  fractionRingMap_algebraMap _ _ _

variable [Algebra E K] [Algebra F K]

/-- 係数写像が両立すれば、変数のq乗による分数体写像も合成と両立する。 -/
theorem powerSeriesFractionMap_comp_coefficientMap (φ : E →+* F)
    (hφ : (algebraMap F K).comp φ = algebraMap E K) (q : ℕ) (hq : 0 < q) :
    (powerSeriesFractionMap (σ := σ) (E := F) (K := K) q hq).comp
      (powerSeriesCoefficientFractionMap φ) = powerSeriesFractionMap (E := E) q hq := by
  apply IsFractionRing.ringHom_ext (A := MvPowerSeries σ E)
  intro f
  simp only [RingHom.comp_apply, powerSeriesCoefficientFractionMap_algebraMap,
    powerSeriesFractionMap_algebraMap]
  congr 1
  change MvPowerSeries.expand q (Nat.ne_of_gt hq)
      (MvPowerSeries.map (algebraMap F K) (MvPowerSeries.map φ f)) =
    MvPowerSeries.expand q (Nat.ne_of_gt hq) (MvPowerSeries.map (algebraMap E K) f)
  rw [MvPowerSeries.map_map, hφ]

/-- 変数のq乗による分数体写像の像を、共通分数体の実際の部分体として取る。 -/
def powerSeriesFractionSubfield (E : Type*) [Field E] [Algebra E K] (q : ℕ) (hq : 0 < q) :
    Subfield (FractionRing (MvPowerSeries σ K)) :=
  (powerSeriesFractionMap (σ := σ) (E := E) q hq).fieldRange

/-- 係数の包含に沿って、実際の像の部分体も包含される。 -/
theorem powerSeriesFractionSubfield_le_of_coefficientMap (φ : E →+* F)
    (hφ : (algebraMap F K).comp φ = algebraMap E K) (q : ℕ) (hq : 0 < q) :
    powerSeriesFractionSubfield (σ := σ) (K := K) E q hq ≤
      powerSeriesFractionSubfield F q hq := by
  rintro x ⟨a, rfl⟩
  refine ⟨powerSeriesCoefficientFractionMap φ a, ?_⟩
  exact congrArg (fun f ↦ f a) (powerSeriesFractionMap_comp_coefficientMap φ hφ q hq)


/-- 係数基底に1が含まれるなら、分数体の像に属す冪級数は元の冪級数写像の像に属す。 -/
theorem algebraMap_mem_powerSeriesFractionSubfield_iff_of_basis_one
    {α : Type*} [Finite σ] [Finite α] (B : Module.Basis α E K) (a : α)
    (ha : B a = 1) (q : ℕ) (hq : 0 < q) (f : MvPowerSeries σ K) :
    algebraMap _ (FractionRing (MvPowerSeries σ K)) f ∈
        powerSeriesFractionSubfield (σ := σ) (K := K) E q hq ↔
      f ∈ Set.range (powerSeriesExpandMap (σ := σ) (E := E) (K := K) q hq) := by
  let : Fintype σ := Fintype.ofFinite σ
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) := (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  let r : σ → Fin q := fun _ ↦ ⟨0, hq⟩
  have hr : powerSeriesResidueExponent q r = 0 := by ext i; rfl
  have hB : powerSeriesExpansionBasis B q hq (r, a) = 1 := by
    rw [powerSeriesExpansionBasis_apply, ha, hr, MvPowerSeries.monomial_zero_one]
  exact algebraMap_mem_fractionRingMap_fieldRange_iff_of_basis_one
    (powerSeriesExpandMap_injective q hq (RingHom.injective _))
    (powerSeriesExpansionBasis B q hq) (r, a) hB f

end SerrePositivity
