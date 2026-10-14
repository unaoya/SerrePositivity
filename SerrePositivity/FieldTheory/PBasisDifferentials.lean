module

public import SerrePositivity.FieldTheory.PBasis
public import SerrePositivity.CommutativeAlgebra.DerivationSpan

/-! # p-basis の通常の微分による生成

通常の微分だけを扱う。完備微分の生成性・有限性へ読み替えない。
微分の独立性と偏導分の実構成は `PBasisPartialDerivation` で扱う。
-/

@[expose] public section
namespace SerrePositivity

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable {ι : Type*} {b : ι → K}

/-- p-basis 上の導分の値は、全ての値と同じ空間を生成する。 -/
theorem IsPBasis.span_range_derivation
    {V : Type*} [AddCommGroup V] [Module K V] [Module (pPowerSubfield K p) V]
    (hb : IsPBasis K p b) (δ : Derivation (pPowerSubfield K p) K V) :
    Submodule.span K (Set.range δ) = Submodule.span K (Set.range (fun i ↦ δ (b i))) := by
  rw [span_range_derivation_eq_span_of_adjoin_eq_top δ _ hb.adjoin_eq_top]
  rw [← Set.range_comp]
  rfl

/-- p-basis の微分は通常の相対 Kähler 微分を生成する。 -/
theorem IsPBasis.span_kaehlerDifferential (hb : IsPBasis K p b) :
    Submodule.span K
      (Set.range (fun i ↦ KaehlerDifferential.D (pPowerSubfield K p) K (b i))) = ⊤ := by
  rw [← hb.span_range_derivation (KaehlerDifferential.D (pPowerSubfield K p) K)]
  exact KaehlerDifferential.span_range_derivation _ _

/-- 有限 p-basis の場合に限って、通常の微分の有限生成性を供給する。 -/
theorem IsPBasis.finite_kaehlerDifferential [Finite ι] (hb : IsPBasis K p b) :
    Module.Finite K (KaehlerDifferential (pPowerSubfield K p) K) := by
  apply Module.finite_def.mpr
  rw [← hb.span_kaehlerDifferential]
  exact Submodule.fg_span (Set.finite_range _)

/-- 任意の基礎環上の導分も、p 乗部分体の元を消す。 -/
theorem derivation_eq_zero_on_pPowerSubfield
    {R V : Type*} [CommRing R] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    (δ : Derivation R K V) (x : K) (hx : x ∈ pPowerSubfield K p) : δ x = 0 := by
  obtain ⟨y, rfl⟩ := (mem_pPowerSubfield K p x).mp hx
  exact derivation_pow_char_eq_zero p δ y

/-- 任意の基礎環上の導分を、同じ写像のまま p 乗部分体上の導分にする。
p 乗部分体の作用は、K の作用から制限した標準作用を用いる。 -/
def derivationOverPowers
    {R V : Type*} [CommRing R] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    (δ : Derivation R K V) : Derivation (pPowerSubfield K p) K V where
  toFun := δ
  map_add' := map_add δ
  map_smul' c x := by
    rw [Algebra.smul_def]
    have hc : δ (algebraMap (pPowerSubfield K p) K c) = 0 :=
      derivation_eq_zero_on_pPowerSubfield δ _ c.property
    rw [δ.leibniz, hc, smul_zero, add_zero]
    rfl
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

@[simp] theorem derivationOverPowers_apply
    {R V : Type*} [CommRing R] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    (δ : Derivation R K V) (x : K) : derivationOverPowers (p := p) δ x = δ x := rfl

/-- p-basis の値による生成性は、任意の基礎環上の導分にも適用できる。 -/
theorem IsPBasis.span_range_derivation_over_base
    {R V : Type*} [CommRing R] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V]
    (hb : IsPBasis K p b) (δ : Derivation R K V) :
    Submodule.span K (Set.range δ) = Submodule.span K (Set.range (fun i ↦ δ (b i))) :=
  hb.span_range_derivation (derivationOverPowers (p := p) δ)

/-- 任意の基礎環上の通常微分も p-basis の微分で生成される。 -/
theorem IsPBasis.span_kaehlerDifferential_over_base
    {R : Type*} [CommRing R] [Algebra R K] (hb : IsPBasis K p b) :
    Submodule.span K (Set.range (fun i ↦ KaehlerDifferential.D R K (b i))) = ⊤ := by
  rw [← hb.span_range_derivation_over_base (KaehlerDifferential.D R K)]
  exact KaehlerDifferential.span_range_derivation _ _

end SerrePositivity
