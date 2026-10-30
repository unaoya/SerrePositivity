module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Expansion
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.FieldTheory.SeparableBaseChange
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # 冪級数の有限拡大の分数体

概要：体 `E ⊆ K` の有限基底 `B` と `q > 0` について、`E[[X]] → K[[T]]`（係数拡大と `X_i ↦ T_i^q`）を
分数体の写像へ延長し、同じ単項式 `T^r · B a` の像が分数体拡大の基底になること、次数が `q^{|σ|} · |B|`
であることを示す。係数写像の包含に沿って像の部分体も包含され、`B` が `1` を含めば分数体の像と元の冪級数環の
交わりは元の写像の像に一致する。
方針：冪級数環の基底（`PowerSeries/Expansion`）を、代数的な整域拡大の基底を分数体へ移す一般論
（`fractionRingBasisOfAlgebraic`）に渡す。
規約：展開写像は標準的な代数構造ではないので、分数体の写像は Mathlib の `IsLocalization.map` で与える。
使われ方：中間係数体に沿う分数体族（`CofiniteFraction*`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Basis

variable {E K σ α : Type*} [Field E] [Field K] [Algebra E K]

/-- X_i↦T_i^qの単射を分数体へ延長する。 -/
def powerSeriesFractionMap (q : ℕ) (hq : 0 < q) :
    FractionRing (MvPowerSeries σ E) →+* FractionRing (MvPowerSeries σ K) :=
  IsLocalization.map (M := nonZeroDivisors (MvPowerSeries σ E))
    (T := nonZeroDivisors (MvPowerSeries σ K)) (FractionRing (MvPowerSeries σ K))
    (powerSeriesExpandMap q hq)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (powerSeriesExpandMap_injective q hq (RingHom.injective _)))

@[simp] theorem powerSeriesFractionMap_algebraMap (q : ℕ) (hq : 0 < q)
    (f : MvPowerSeries σ E) :
    powerSeriesFractionMap (K := K) q hq
      (algebraMap _ (FractionRing (MvPowerSeries σ E)) f) =
      algebraMap _ (FractionRing (MvPowerSeries σ K)) (powerSeriesExpandMap (K := K) q hq f) :=
  IsLocalization.map_eq _ _

section Basis
variable [Fintype σ] [Finite α] (q : ℕ) (hq : 0 < q)

/-- 同じ単項式の像から構成した、分数体拡大の実際の基底。 -/
def powerSeriesFractionBasis (B : Module.Basis α E K) :
    letI : Algebra (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
      (powerSeriesFractionMap q hq).toAlgebra
    Module.Basis ((σ → Fin q) × α)
      (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) := by
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
    (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  let : Algebra (MvPowerSeries σ E) (FractionRing (MvPowerSeries σ K)) :=
    ((algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))).comp
      (powerSeriesExpandMap q hq)).toAlgebra
  let : SMul (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) :=
    (inferInstance : Algebra (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))).toSMul
  let : SMul (MvPowerSeries σ E) (FractionRing (MvPowerSeries σ K)) :=
    (inferInstance : Algebra (MvPowerSeries σ E) (FractionRing (MvPowerSeries σ K))).toSMul
  let : IsScalarTower (MvPowerSeries σ E) (MvPowerSeries σ K)
      (FractionRing (MvPowerSeries σ K)) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
    (powerSeriesFractionMap q hq).toAlgebra
  let : IsScalarTower (MvPowerSeries σ E) (FractionRing (MvPowerSeries σ E))
      (FractionRing (MvPowerSeries σ K)) :=
    IsScalarTower.of_algebraMap_eq (fun f ↦ (powerSeriesFractionMap_algebraMap q hq f).symm)
  let : Module.Finite (MvPowerSeries σ E) (MvPowerSeries σ K) :=
    powerSeriesExpandMap_finite B q hq
  exact fractionRingBasisOfAlgebraic (powerSeriesExpansionBasis B q hq)

@[simp] theorem powerSeriesFractionBasis_apply (B : Module.Basis α E K)
    (x : (σ → Fin q) × α) :
    powerSeriesFractionBasis q hq B x =
      algebraMap _ (FractionRing (MvPowerSeries σ K))
        (MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2)) := by
  simp only [powerSeriesFractionBasis, fractionRingBasisOfAlgebraic_apply,
    powerSeriesExpansionBasis_apply]

/-- 分数体へ移しても、拡大次数は元の有限基底の大きさと一致する。 -/
theorem finrank_powerSeriesFractionField (B : Module.Basis α E K) :
    letI : Algebra (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
      (powerSeriesFractionMap q hq).toAlgebra
    Module.finrank (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) =
      q ^ Fintype.card σ * Nat.card α := by
  let : Algebra (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
    (powerSeriesFractionMap q hq).toAlgebra
  classical
  let : Fintype α := Fintype.ofFinite α
  rw [Module.finrank_eq_card_basis (powerSeriesFractionBasis (σ := σ) q hq B)]
  simp [Nat.card_eq_fintype_card]

end Basis

end Basis

section Subfield

variable {E F K σ : Type*} [Field E] [Field F] [Field K]

/-- 係数写像だけを作用させ、変数を保つ分数体の写像。 -/
def powerSeriesCoefficientFractionMap (φ : E →+* F) :
    FractionRing (MvPowerSeries σ E) →+* FractionRing (MvPowerSeries σ F) :=
  IsLocalization.map (M := nonZeroDivisors (MvPowerSeries σ E))
    (T := nonZeroDivisors (MvPowerSeries σ F)) (FractionRing (MvPowerSeries σ F))
    (MvPowerSeries.map φ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (by
      intro f g hfg
      ext d
      apply φ.injective
      simpa only [MvPowerSeries.coeff_map] using congrArg (MvPowerSeries.coeff d) hfg))

@[simp] theorem powerSeriesCoefficientFractionMap_algebraMap (φ : E →+* F)
    (f : MvPowerSeries σ E) :
    powerSeriesCoefficientFractionMap φ (algebraMap _ (FractionRing (MvPowerSeries σ E)) f) =
      algebraMap _ (FractionRing (MvPowerSeries σ F)) (MvPowerSeries.map φ f) :=
  IsLocalization.map_eq _ _

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
  have hinj : Function.Injective (algebraMap (MvPowerSeries σ E) (MvPowerSeries σ K)) :=
    powerSeriesExpandMap_injective q hq (RingHom.injective _)
  have hφ : ∀ g : MvPowerSeries σ E, powerSeriesFractionMap (K := K) q hq
      (algebraMap _ (FractionRing (MvPowerSeries σ E)) g) =
      algebraMap _ (FractionRing (MvPowerSeries σ K))
        (algebraMap (MvPowerSeries σ E) (MvPowerSeries σ K) g) :=
    powerSeriesFractionMap_algebraMap q hq
  exact algebraMap_mem_fieldRange_iff_of_basis_one (K := FractionRing (MvPowerSeries σ E))
    (L := FractionRing (MvPowerSeries σ K)) hinj (powerSeriesFractionMap q hq) hφ
    (powerSeriesExpansionBasis B q hq) (r, a) hB f

end Subfield

end SerrePositivity
