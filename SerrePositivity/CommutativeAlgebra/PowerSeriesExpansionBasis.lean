module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesFiniteExpansion
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # 係数基底と指数剰余からの冪級数加群の基底

作用はE[[X]]→K[[T]]、X_i↦T_i^qによる係数制限。
剰余と係数座標を抽出して、前段の生成族の独立性を確認する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {E K σ α : Type*} [CommRing E] [CommRing K] [Algebra E K]
  [Fintype σ]

/-- 指数q·d+rの係数のB座標を集める。 -/
def powerSeriesExpansionCoordinate (B : Module.Basis α E K) (q : ℕ)
    (r : σ → Fin q) (a : α) (f : MvPowerSeries σ K) : MvPowerSeries σ E :=
  powerSeriesCoefficientComponent B (powerSeriesResidueComponent q r f) a

open Classical in
/-- 一つの剰余単項式と係数基底元による項の係数。 -/
theorem coeff_powerSeriesExpansionTerm (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q)
    (r : σ → Fin q) (a : α) (g : MvPowerSeries σ E) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d
      (MvPowerSeries.monomial (powerSeriesResidueExponent q r) (B a) *
        powerSeriesExpandMap q hq g) =
      if r = powerSeriesResidueIndex q hq d then
        B a * algebraMap E K (MvPowerSeries.coeff (powerSeriesQuotientExponent q d) g)
      else 0 := by
  have he : MvPowerSeries.monomial (powerSeriesResidueExponent q r) (B a) *
      powerSeriesExpandMap q hq g =
      MvPowerSeries.monomial (powerSeriesResidueExponent q r) 1 *
        MvPowerSeries.expand q (Nat.ne_of_gt hq)
          (MvPowerSeries.C (B a) * MvPowerSeries.map (algebraMap E K) g) := by
    rw [map_mul, MvPowerSeries.expand_C, ← mul_assoc]
    change _ = (MvPowerSeries.monomial _ 1 * MvPowerSeries.monomial 0 (B a)) * _
    rw [MvPowerSeries.monomial_mul_monomial, add_zero, one_mul]
    rfl
  rw [he, coeff_powerSeriesResidueExpansion q hq]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map]

section Coordinates
variable [Fintype α]

open Classical in
/-- 有限和の座標抽出は、指定した元の係数冪級数へ戻る。 -/
theorem powerSeriesExpansionCoordinate_sum (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q)
    (g : (σ → Fin q) × α → MvPowerSeries σ E) (r : σ → Fin q) (a : α) :
    powerSeriesExpansionCoordinate B q r a
      (∑ x, MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2) *
        powerSeriesExpandMap q hq (g x)) = g (r, a) := by
  ext d
  have hcoeff : MvPowerSeries.coeff (q • d + powerSeriesResidueExponent q r)
      (∑ x : (σ → Fin q) × α,
        MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2) *
          powerSeriesExpandMap q hq (g x)) =
      ∑ a' : α, B a' * algebraMap E K (MvPowerSeries.coeff d (g (r, a'))) := by
    simp only [Fintype.sum_prod_type, map_sum, coeff_powerSeriesExpansionTerm,
      powerSeriesResidueIndex_scale_add, powerSeriesQuotientExponent_scale_add q hq]
    simp
  have hc (a' : α) (c : E) : B.repr (B a' * algebraMap E K c) a =
      if a' = a then c else 0 := by
    rw [mul_comm, ← Algebra.smul_def, map_smul]
    simp [Finsupp.single_apply]
  calc
    _ = B.repr (MvPowerSeries.coeff (q • d + powerSeriesResidueExponent q r)
        (∑ x : (σ → Fin q) × α,
          MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2) *
            powerSeriesExpandMap q hq (g x))) a := rfl
    _ = B.repr (∑ a' : α, B a' * algebraMap E K
        (MvPowerSeries.coeff d (g (r, a')))) a := congrArg (fun x ↦ B.repr x a) hcoeff
    _ = _ := by simp only [map_sum, Finsupp.finsetSum_apply, hc]; simp

end Coordinates

variable [Finite α]

/-- 指定した冪級数係数作用について、剰余単項式と係数基底元は独立。 -/
theorem powerSeriesExpansion_linearIndependent (B : Module.Basis α E K) (q : ℕ)
    (hq : 0 < q) :
    letI : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
      (powerSeriesExpandMap q hq).toAlgebra
    letI : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
    LinearIndependent (MvPowerSeries σ E)
      (fun x : (σ → Fin q) × α ↦
        MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2)) := by
  classical
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
    (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  let : Fintype α := Fintype.ofFinite α
  apply Fintype.linearIndependent_iff.mpr
  intro g hg x
  have hgsum : (∑ y : (σ → Fin q) × α,
      MvPowerSeries.monomial (powerSeriesResidueExponent q y.1) (B y.2) *
        powerSeriesExpandMap q hq (g y)) = 0 := by
    simpa only [powerSeriesExpansionModule, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, mul_comm] using hg
  calc
    g x = powerSeriesExpansionCoordinate B q x.1 x.2
        (∑ y : (σ → Fin q) × α,
          MvPowerSeries.monomial (powerSeriesResidueExponent q y.1) (B y.2) *
            powerSeriesExpandMap q hq (g y)) :=
      (powerSeriesExpansionCoordinate_sum B q hq g x.1 x.2).symm
    _ = powerSeriesExpansionCoordinate B q x.1 x.2 0 :=
      congrArg (powerSeriesExpansionCoordinate B q x.1 x.2) hgsum
    _ = 0 := by
      ext d
      change B.repr (0 : K) x.2 = 0
      simp

/-- E[[X]]→K[[T]]、X_i↦T_i^qに沿う実際の加群基底。 -/
def powerSeriesExpansionBasis (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) :
    letI : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
      (powerSeriesExpandMap q hq).toAlgebra
    letI : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
    Module.Basis ((σ → Fin q) × α) (MvPowerSeries σ E) (MvPowerSeries σ K) := by
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
    (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  exact Module.Basis.mk (powerSeriesExpansion_linearIndependent B q hq)
    (by rw [powerSeriesExpansion_span B q hq])

@[simp] theorem powerSeriesExpansionBasis_apply (B : Module.Basis α E K) (q : ℕ)
    (hq : 0 < q) (x : (σ → Fin q) × α) :
    powerSeriesExpansionBasis B q hq x =
      MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2) := by
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
    (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  exact Module.Basis.mk_apply (powerSeriesExpansion_linearIndependent B q hq)
    (by rw [powerSeriesExpansion_span B q hq]) x

/-- 非零係数環では、基底の添字から自由加群の階数を正確に計算する。 -/
theorem powerSeriesExpansion_finrank [Nontrivial E]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) :
    letI : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
      (powerSeriesExpandMap q hq).toAlgebra
    letI : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
    Module.finrank (MvPowerSeries σ E) (MvPowerSeries σ K) =
      q ^ Fintype.card σ * Nat.card α := by
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
    (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  classical
  let : Fintype α := Fintype.ofFinite α
  rw [Module.finrank_eq_card_basis (powerSeriesExpansionBasis B q hq)]
  simp [Nat.card_eq_fintype_card]

end SerrePositivity
