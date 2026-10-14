module

public import SerrePositivity.CommutativeAlgebra.FractionRingBasis
public import SerrePositivity.CommutativeAlgebra.PowerSeriesExpansionBasis
public import SerrePositivity.CommutativeAlgebra.PowerSeriesDomain

/-! # 冪級数の有限基底を分数体へ移す

係数基底と変数のq乗による写像そのものを分数体へ延長し、
同じ単項式の像を基底として拡大次数を計算する。分離性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {E K σ α : Type*} [Field E] [Field K] [Algebra E K]

/-- X_i↦T_i^qの単射を分数体へ延長する。 -/
def powerSeriesFractionMap (q : ℕ) (hq : 0 < q) :
    FractionRing (MvPowerSeries σ E) →+* FractionRing (MvPowerSeries σ K) :=
  fractionRingMap (powerSeriesExpandMap q hq)
    (powerSeriesExpandMap_injective q hq (RingHom.injective _))

@[simp] theorem powerSeriesFractionMap_algebraMap (q : ℕ) (hq : 0 < q)
    (f : MvPowerSeries σ E) :
    powerSeriesFractionMap (K := K) q hq
      (algebraMap _ (FractionRing (MvPowerSeries σ E)) f) =
      algebraMap _ (FractionRing (MvPowerSeries σ K)) (powerSeriesExpandMap (K := K) q hq f) :=
  fractionRingMap_algebraMap _ _ _

/-- 延長した冪級数写像による分数体の係数作用。 -/
@[instance_reducible] def powerSeriesFractionModule (q : ℕ) (hq : 0 < q) :
    Module (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
  @Algebra.toModule _ _ _ _ (powerSeriesFractionMap q hq).toAlgebra

section Basis
variable [Fintype σ] [Finite α] (q : ℕ) (hq : 0 < q)

/-- 同じ単項式の像から構成した、分数体拡大の実際の基底。 -/
def powerSeriesFractionBasis (B : Module.Basis α E K) :
    letI : Algebra (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
      (powerSeriesFractionMap q hq).toAlgebra
    letI : Module (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
      powerSeriesFractionModule q hq
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
  let : Module (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
    powerSeriesFractionModule q hq
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
    letI : Module (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
      powerSeriesFractionModule q hq
    Module.finrank (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) =
      q ^ Fintype.card σ * Nat.card α := by
  let : Algebra (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
    (powerSeriesFractionMap q hq).toAlgebra
  let : Module (FractionRing (MvPowerSeries σ E)) (FractionRing (MvPowerSeries σ K)) :=
    powerSeriesFractionModule q hq
  classical
  let : Fintype α := Fintype.ofFinite α
  rw [Module.finrank_eq_card_basis (powerSeriesFractionBasis (σ := σ) q hq B)]
  simp [Nat.card_eq_fintype_card]

end Basis
end SerrePositivity
