module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesCoefficientBasis
public import SerrePositivity.CommutativeAlgebra.PowerSeriesResidueDecomposition
public import Mathlib.RingTheory.RingHom.Finite

/-! # 係数基底と指数剰余による有限な冪級数拡大

E上のKの有限基底と正の整数qから、E[[X]]→K[[T]]、X_i↦T_i^qを構成する。
有限な変数族では係数基底と剰余単項式による生成性を実際に確認する。
完全体性や標数の仮定は使わない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {E K σ α : Type*} [CommRing E] [CommRing K] [Algebra E K]

/-- 係数の写像と変数のq乗による冪級数環の写像。 -/
def powerSeriesExpandMap (q : ℕ) (hq : 0 < q) :
    MvPowerSeries σ E →+* MvPowerSeries σ K :=
  (MvPowerSeries.expand q (Nat.ne_of_gt hq)).toRingHom.comp
    (MvPowerSeries.map (algebraMap E K))

/-- 変数のq乗による写像に沿う加群作用。同じ環の自己作用とも区別する。 -/
@[instance_reducible] def powerSeriesExpansionModule (q : ℕ) (hq : 0 < q) :
    Module (MvPowerSeries σ E) (MvPowerSeries σ K) :=
  @Algebra.toModule _ _ _ _ (powerSeriesExpandMap q hq).toAlgebra

/-- 指定した加群の実際のスカラー作用は、展開写像の像による乗法。 -/
theorem powerSeriesExpansion_smul (q : ℕ) (hq : 0 < q)
    (f : MvPowerSeries σ E) (g : MvPowerSeries σ K) :
    letI : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
    letI : SMul (MvPowerSeries σ E) (MvPowerSeries σ K) :=
      (powerSeriesExpansionModule q hq).toSMul
    f • g = powerSeriesExpandMap q hq f * g := rfl

@[simp] theorem powerSeriesExpandMap_C (q : ℕ) (hq : 0 < q) (a : E) :
    powerSeriesExpandMap (σ := σ) (K := K) q hq (MvPowerSeries.C a) =
      MvPowerSeries.C (algebraMap E K a) := by
  simp [powerSeriesExpandMap, MvPowerSeries.expand_C]

@[simp] theorem powerSeriesExpandMap_X (q : ℕ) (hq : 0 < q) (i : σ) :
    powerSeriesExpandMap (E := E) (K := K) q hq (MvPowerSeries.X i) =
      MvPowerSeries.X i ^ q := by
  simp [powerSeriesExpandMap, MvPowerSeries.expand_X]

/-- 係数写像が単射なら、変数の正の冪による写像も単射。変数の有限性は不要。 -/
theorem powerSeriesExpandMap_injective (q : ℕ) (hq : 0 < q)
    (hEK : Function.Injective (algebraMap E K)) :
    Function.Injective (powerSeriesExpandMap (σ := σ) (E := E) (K := K) q hq) := by
  intro f g hfg
  ext d
  apply hEK
  have h := congrArg (MvPowerSeries.coeff (q • d)) hfg
  change MvPowerSeries.coeff (q • d)
      (MvPowerSeries.expand q (Nat.ne_of_gt hq) (MvPowerSeries.map (algebraMap E K) f)) =
    MvPowerSeries.coeff (q • d)
      (MvPowerSeries.expand q (Nat.ne_of_gt hq) (MvPowerSeries.map (algebraMap E K) g)) at h
  simpa only [MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map] using h

open Classical in
/-- 係数の基底と変数の剰余単項式から、実際の有限和を構成する。 -/
theorem powerSeries_coefficient_residue_decomposition [Fintype σ] [Fintype α]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) (f : MvPowerSeries σ K) :
    f = ∑ r : σ → Fin q, ∑ a : α,
      MvPowerSeries.monomial (powerSeriesResidueExponent q r) (B a) *
        powerSeriesExpandMap q hq
          (powerSeriesCoefficientComponent B (powerSeriesResidueComponent q r f) a) := by
  trans ∑ r : σ → Fin q,
    MvPowerSeries.monomial (powerSeriesResidueExponent q r) 1 *
      MvPowerSeries.expand q (Nat.ne_of_gt hq) (powerSeriesResidueComponent q r f)
  · exact powerSeries_residue_decomposition q hq f
  apply Finset.sum_congr rfl
  intro r _
  conv_lhs => rw [powerSeries_coefficient_decomposition B (powerSeriesResidueComponent q r f)]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul, MvPowerSeries.expand_C, ← mul_assoc]
  change (MvPowerSeries.monomial _ 1 * MvPowerSeries.monomial 0 (B a)) * _ = _
  rw [MvPowerSeries.monomial_mul_monomial, add_zero, one_mul]
  rfl

/-- 指定した係数作用のもとで、剰余単項式の線形包は全体になる。 -/
theorem powerSeriesExpansion_span [Fintype σ] [Finite α]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) :
    letI : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
      (powerSeriesExpandMap q hq).toAlgebra
    letI : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
    Submodule.span (MvPowerSeries σ E)
      (Set.range (fun x : (σ → Fin q) × α ↦
        MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2))) = ⊤ := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let F := powerSeriesExpandMap (σ := σ) (E := E) (K := K) q hq
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) := F.toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  let v : (σ → Fin q) × α → MvPowerSeries σ K :=
    fun x ↦ MvPowerSeries.monomial (powerSeriesResidueExponent q x.1) (B x.2)
  let V := Submodule.span (MvPowerSeries σ E) (Set.range v)
  have hV : V = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro f
    rw [powerSeries_coefficient_residue_decomposition B q hq f]
    apply Submodule.sum_mem
    intro r _
    apply Submodule.sum_mem
    intro a _
    have h := V.smul_mem
      (powerSeriesCoefficientComponent B (powerSeriesResidueComponent q r f) a)
      (Submodule.subset_span (Set.mem_range_self (r, a)))
    change F _ * v (r, a) ∈ V at h
    simpa only [v, F, mul_comm] using h
  exact hV


/-- 有限係数基底と有限変数の剰余単項式から、同じ写像の有限性を証明する。 -/
theorem powerSeriesExpandMap_finite [Finite σ] [Finite α]
    (B : Module.Basis α E K) (q : ℕ) (hq : 0 < q) :
    (powerSeriesExpandMap (σ := σ) (E := E) (K := K) q hq).Finite := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype α := Fintype.ofFinite α
  let : Algebra (MvPowerSeries σ E) (MvPowerSeries σ K) :=
    (powerSeriesExpandMap q hq).toAlgebra
  let : Module (MvPowerSeries σ E) (MvPowerSeries σ K) := powerSeriesExpansionModule q hq
  change Module.Finite (MvPowerSeries σ E) (MvPowerSeries σ K)
  constructor
  rw [← powerSeriesExpansion_span B q hq]
  exact Submodule.fg_span (Set.finite_range _)

end SerrePositivity
