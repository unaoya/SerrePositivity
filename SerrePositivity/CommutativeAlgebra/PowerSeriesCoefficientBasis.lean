module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # 有限な係数基底による冪級数の一意な分解

各係数を同じ有限基底で展開し、その座標を冪級数へまとめる。
係数環の体性・完全性や変数の有限性は要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {E K σ α : Type*} [CommRing E] [CommRing K] [Algebra E K]

/-- 各係数の指定基底に関する座標を集めた冪級数。 -/
def powerSeriesCoefficientComponent (B : Module.Basis α E K)
    (f : MvPowerSeries σ K) (a : α) : MvPowerSeries σ E :=
  fun d ↦ B.repr (MvPowerSeries.coeff d f) a

@[simp] theorem coeff_powerSeriesCoefficientComponent (B : Module.Basis α E K)
    (f : MvPowerSeries σ K) (a : α) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (powerSeriesCoefficientComponent B f a) =
      B.repr (MvPowerSeries.coeff d f) a := rfl

/-- 有限な係数基底の展開を、そのまま冪級数へ持ち上げる。 -/
theorem powerSeries_coefficient_decomposition [Fintype α] (B : Module.Basis α E K)
    (f : MvPowerSeries σ K) :
    f = ∑ a, MvPowerSeries.C (B a) *
      MvPowerSeries.map (algebraMap E K) (powerSeriesCoefficientComponent B f a) := by
  ext d
  simpa only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map,
    coeff_powerSeriesCoefficientComponent, Algebra.smul_def, mul_comm] using
    (B.sum_repr (MvPowerSeries.coeff d f)).symm

/-- 指定基底の係数冪級数による展開は一意。 -/
theorem powerSeries_existsUnique_coefficient_decomposition [Fintype α] (B : Module.Basis α E K)
    (f : MvPowerSeries σ K) :
    ∃! g : α → MvPowerSeries σ E,
      f = ∑ a, MvPowerSeries.C (B a) * MvPowerSeries.map (algebraMap E K) (g a) := by
  refine ⟨powerSeriesCoefficientComponent B f, powerSeries_coefficient_decomposition B f, ?_⟩
  intro g hg
  funext a
  ext d
  have hs : B.equivFun.symm (fun a ↦ MvPowerSeries.coeff d (g a)) =
      MvPowerSeries.coeff d f := by
    rw [B.equivFun_symm_apply]
    simpa only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map,
      Algebra.smul_def, mul_comm] using (congrArg (MvPowerSeries.coeff d) hg).symm
  have he := congrArg B.equivFun hs
  have he' : (fun a ↦ MvPowerSeries.coeff d (g a)) =
      B.equivFun (MvPowerSeries.coeff d f) :=
    (B.equivFun.apply_symm_apply _).symm.trans he
  exact congrFun he' a

end SerrePositivity
