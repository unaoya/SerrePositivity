module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Expansion
public import SerrePositivity.FieldTheory.PBasisCofiniteField

/-! # 中間係数体とパラメータのp乗に沿う冪級数の有限拡大

κ_e[[X]]→κ[[T]]、X_i↦T_i^pについて、相対p単項式と指数剰余による生成性を確認する。
生成性・有限性・加群基底と正確な自由加群の階数を確認する。
分数体拡大の次数や分離性はこのファイルではまだ主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} {b : ι → K}

open Classical in
/-- κ_e係数の実際の冪級数の有限和として、任意のκ係数の冪級数を展開する。 -/
theorem IsPBasis.powerSeries_cofinite_decomposition [Fintype σ]
    (hb : IsPBasis K p b) (e : Finset ι) (f : MvPowerSeries σ K) :
    f = ∑ r : σ → Fin p, ∑ a : PExponent p e,
      MvPowerSeries.monomial (powerSeriesResidueExponent p r)
        (pMonomial (fun i : e ↦ b i) a) *
        powerSeriesExpandMap p (Fact.out : p.Prime).pos
          (powerSeriesCoefficientComponent (hb.cofiniteMonomialBasis e)
            (powerSeriesResidueComponent p r f) a) := by
  simpa only [IsPBasis.cofiniteMonomialBasis_apply] using
    powerSeries_coefficient_residue_decomposition (hb.cofiniteMonomialBasis e)
      p (Fact.out : p.Prime).pos f

/-- κ_e[[X]]→κ[[T]]、X_i↦T_i^pは同じ係数写像を保つ有限単射。 -/
theorem IsPBasis.powerSeries_cofinite_expand_injective_finite [Finite σ]
    (hb : IsPBasis K p b) (e : Finset ι) :
    Function.Injective
      (powerSeriesExpandMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
        (K := K) p (Fact.out : p.Prime).pos) ∧
      (powerSeriesExpandMap (σ := σ) (E := pBasisCofiniteField (p := p) b e)
        (K := K) p (Fact.out : p.Prime).pos).Finite := by
  exact ⟨powerSeriesExpandMap_injective p (Fact.out : p.Prime).pos (RingHom.injective _),
    powerSeriesExpandMap_finite (hb.cofiniteMonomialBasis e) p (Fact.out : p.Prime).pos⟩

/-- 中間係数体の相対p単項式と変数の剰余単項式からの実際の冪級数基底。 -/
def IsPBasis.cofinitePowerSeriesBasis [Fintype σ] (hb : IsPBasis K p b) (e : Finset ι) :
    letI : Algebra (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
        (MvPowerSeries σ K) := (powerSeriesExpandMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
        (MvPowerSeries σ K) := powerSeriesExpansionModule p (Fact.out : p.Prime).pos
    Module.Basis ((σ → Fin p) × PExponent p e)
      (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)) (MvPowerSeries σ K) :=
  powerSeriesExpansionBasis (hb.cofiniteMonomialBasis e) p (Fact.out : p.Prime).pos

@[simp] theorem IsPBasis.cofinitePowerSeriesBasis_apply [Fintype σ]
    (hb : IsPBasis K p b) (e : Finset ι) (x : (σ → Fin p) × PExponent p e) :
    hb.cofinitePowerSeriesBasis (σ := σ) e x =
      MvPowerSeries.monomial (powerSeriesResidueExponent p x.1)
        (pMonomial (fun i : e ↦ b i) x.2) := by
  exact (powerSeriesExpansionBasis_apply (hb.cofiniteMonomialBasis e)
    p (Fact.out : p.Prime).pos x).trans
      (congrArg (MvPowerSeries.monomial _) (hb.cofiniteMonomialBasis_apply e x.2))

/-- h個の変数と|e|個のp-basis方向を合わせた、正確な冪級数加群の階数。 -/
theorem IsPBasis.finrank_cofinitePowerSeries [Fintype σ]
    (hb : IsPBasis K p b) (e : Finset ι) :
    letI : Algebra (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
        (MvPowerSeries σ K) := (powerSeriesExpandMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
        (MvPowerSeries σ K) := powerSeriesExpansionModule p (Fact.out : p.Prime).pos
    Module.finrank (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
      (MvPowerSeries σ K) = p ^ (Fintype.card σ + e.card) := by
  let : Algebra (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
      (MvPowerSeries σ K) := (powerSeriesExpandMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module (MvPowerSeries σ (pBasisCofiniteField (p := p) b e))
      (MvPowerSeries σ K) := powerSeriesExpansionModule p (Fact.out : p.Prime).pos
  rw [powerSeriesExpansion_finrank (hb.cofiniteMonomialBasis e) p (Fact.out : p.Prime).pos]
  rw [Nat.card_eq_fintype_card, PExponent.card, Fintype.card_coe, pow_add]

end SerrePositivity
