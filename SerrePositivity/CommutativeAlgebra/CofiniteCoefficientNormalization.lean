module

public import SerrePositivity.CommutativeAlgebra.CofiniteCoefficientDifferential
public import SerrePositivity.CommutativeAlgebra.FinitePowerSeriesNormalization

/-! # 中間係数体とパラメータのp乗による有限正規化

κ_eの剰余体への全射性を仮定せず、準素商のκ_e上の有限性を供給して評価を構成する。
同じ評価について有限性・単射性・係数と変数の像を確認する。
分数体拡大の分離性は主張しない。
-/

@[expose] public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 中間係数体とパラメータのp乗から、有限な冪級数評価を構成する。 -/
theorem IsPBasis.exists_finite_cofinite_powerSeries_map
    {K D : Type u} [Field K] [CommRing D] [Algebra K D]
    [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
    {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue D).comp (algebraMap K D)))
    {σ : Type*} [Finite σ] (z : σ → D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ F : MvPowerSeries σ (pBasisCofiniteField (p := p) b e) →+* D,
      F.Finite ∧ (∀ a, F (MvPowerSeries.C a) =
        algebraMap (pBasisCofiniteField (p := p) b e) D a) ∧
        ∀ i, F (MvPowerSeries.X i) = z i ^ p := by
  let E := pBasisCofiniteField (p := p) b e
  let y := fun i ↦ z i ^ p
  let J := Ideal.span (Set.range y)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hJ : J.radical = maximalIdeal D :=
    (radical_span_powers z (fun _ ↦ p) (fun _ ↦ hp)).trans hprimary
  have hJm : J ≤ maximalIdeal D := by rw [← hJ]; exact Ideal.le_radical
  let : IsAdicComplete J D := isAdicComplete_finite_of_le_maximalIdeal J hJm
  let : Module.Finite E (D ⧸ J) := hb.moduleFinite_primaryQuotient_cofiniteField e hres J hJ
  exact exists_finite_powerSeries_map_of_finite_quotient (k := E) y

/-- 次元に等しい個数のパラメータなら、同じ有限評価は単射。 -/
theorem IsPBasis.exists_injective_finite_cofinite_powerSeries_map
    {K D : Type u} [Field K] [CommRing D] [Algebra K D]
    [IsNoetherianRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
    {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue D).comp (algebraMap K D)))
    {h : ℕ} (hdim : ringKrullDim D = h) (z : Fin h → D)
    (hprimary : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    ∃ F : MvPowerSeries (Fin h) (pBasisCofiniteField (p := p) b e) →+* D,
      Function.Injective F ∧ F.Finite ∧ (∀ a, F (MvPowerSeries.C a) =
        algebraMap (pBasisCofiniteField (p := p) b e) D a) ∧
        ∀ i, F (MvPowerSeries.X i) = z i ^ p := by
  obtain ⟨F, hf, hC, hX⟩ := hb.exists_finite_cofinite_powerSeries_map e hres z hprimary
  have hA : ringKrullDim (MvPowerSeries (Fin h) (pBasisCofiniteField (p := p) b e)) = h := by
    rw [ringKrullDim_mvPowerSeries_fin, ringKrullDim_eq_zero_of_field, zero_add]
  exact ⟨F, ringHom_injective_of_finite_of_equal_dimension F hf hA hdim, hf, hC, hX⟩

end SerrePositivity
