module

public import SerrePositivity.CommutativeAlgebra.CofinitePowerSeriesExpansion
public import SerrePositivity.CommutativeAlgebra.PowerSeries.FractionField

/-! # 中間係数体と変数のp乗による分数体拡大の基底と次数

κ_e[[X]]→κ[[T]]、X_i↦T_i^pの同じ写像を分数体へ移す。
相対p単項式と変数の剰余単項式の像を基底として、拡大次数p^(h+|e|)を得る。
分離性や完備微分の次元はこの次数の計算だけからは主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K σ : Type*} [Field K] [Fintype σ] {p : ℕ} [Fact p.Prime] [CharP K p]
  {ι : Type*} {b : ι → K}

/-- 同じ有限単項式の像から構成した、中間係数体に沿う分数体の基底。 -/
def IsPBasis.cofiniteFractionBasis (hb : IsPBasis K p b) (e : Finset ι) :
    letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      powerSeriesFractionModule p (Fact.out : p.Prime).pos
    Module.Basis ((σ → Fin p) × PExponent p e)
      (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) :=
  powerSeriesFractionBasis p (Fact.out : p.Prime).pos (hb.cofiniteMonomialBasis e)

@[simp] theorem IsPBasis.cofiniteFractionBasis_apply
    (hb : IsPBasis K p b) (e : Finset ι) (x : (σ → Fin p) × PExponent p e) :
    hb.cofiniteFractionBasis (σ := σ) e x =
      algebraMap _ (FractionRing (MvPowerSeries σ K))
        (MvPowerSeries.monomial (powerSeriesResidueExponent p x.1)
          (pMonomial (fun i : e ↦ b i) x.2)) := by
  exact (powerSeriesFractionBasis_apply p (Fact.out : p.Prime).pos
    (hb.cofiniteMonomialBasis e) x).trans
      (congrArg (fun c ↦ algebraMap _ (FractionRing (MvPowerSeries σ K))
        (MvPowerSeries.monomial _ c)) (hb.cofiniteMonomialBasis_apply e x.2))

/-- 中間係数体と変数のp乗に沿う分数体拡大の正確な次数。 -/
theorem IsPBasis.finrank_cofiniteFractionField (hb : IsPBasis K p b) (e : Finset ι) :
    letI : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
    letI : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
        (FractionRing (MvPowerSeries σ K)) :=
      powerSeriesFractionModule p (Fact.out : p.Prime).pos
    Module.finrank (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) = p ^ (Fintype.card σ + e.card) := by
  let : Algebra (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) :=
    (powerSeriesFractionMap p (Fact.out : p.Prime).pos).toAlgebra
  let : Module (FractionRing (MvPowerSeries σ (pBasisCofiniteField (p := p) b e)))
      (FractionRing (MvPowerSeries σ K)) := powerSeriesFractionModule p (Fact.out : p.Prime).pos
  rw [finrank_powerSeriesFractionField p (Fact.out : p.Prime).pos (hb.cofiniteMonomialBasis e)]
  rw [Nat.card_eq_fintype_card, PExponent.card, Fintype.card_coe, pow_add]

end SerrePositivity
