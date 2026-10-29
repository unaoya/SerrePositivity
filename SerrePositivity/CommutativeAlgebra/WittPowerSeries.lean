module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Dimension
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Completeness
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.FieldTheory.Perfect

/-! # Witt 係数の冪級数環

概要：完全正標数体 `k` の Witt ベクトル `W(k)` を係数とする有限変数の冪級数環 `W(k)[[X]]` について、
極大イデアルは `(p) + (X)`、次元は `1 + 変数の個数`、正則局所で `(p, X)` 進完備。`p` で割ると `k[[X]]`。
方針：`W(k)` が離散付値環で極大イデアルが `(p)` であることを、冪級数環の一般論（`PowerSeries/*`）に代入する。
規約：剰余体 `k` は完全体。
使われ方：混標数の Cohen 正規化（`WittNormalization*`）と根の塔の mod p 比較（`RootTower`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Structure

open IsLocalRing

/-- Witt係数冪級数の極大イデアルは(p)と全変数で生成される。 -/
theorem wittPowerSeries_maximalIdeal_eq (σ k : Type*) [Finite σ] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k] :
    maximalIdeal (MvPowerSeries σ (WittVector p k)) =
      Ideal.span {(p : MvPowerSeries σ (WittVector p k))} ⊔
        Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := WittVector p k))) := by
  rw [powerSeries_maximalIdeal_eq, (WittVector.irreducible p).maximalIdeal_eq,
    Ideal.map_span]
  simp only [Set.image_singleton, map_natCast]


/-- 完全正標数体のWitt係数冪級数環の次元は1+変数の個数。 -/
theorem ringKrullDim_wittPowerSeries (σ k : Type*) [Fintype σ] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k] :
    ringKrullDim (MvPowerSeries σ (WittVector p k)) = 1 + Fintype.card σ := by
  rw [ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]

/-- 完全正標数体のWitt係数冪級数環は正則局所環。 -/
theorem isRegularLocalRing_wittPowerSeries (σ k : Type*) [Finite σ] [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k] :
    IsRegularLocalRing (MvPowerSeries σ (WittVector p k)) :=
  isRegularLocalRing_mvPowerSeries σ (WittVector p k)

/-- 完全正標数体のWitt係数冪級数は(p,X)進完備。 -/
theorem isAdicComplete_wittPowerSeries_p_sup_variables
    (σ k : Type*) [Finite σ] [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectField k] :
    IsAdicComplete (Ideal.span {(p : MvPowerSeries σ (WittVector p k))} ⊔
      Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := WittVector p k))))
      (MvPowerSeries σ (WittVector p k)) := by
  have h := isAdicComplete_powerSeries_coefficients_sup_variables σ (WittVector p k)
    (Ideal.span {(p : WittVector p k)})
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h

end Structure

section ModP

universe u v

/-- 完全標数p係数のWitt冪級数環をpで割ると、元の係数の冪級数環となる。 -/
def wittPowerSeriesModPEquiv (σ : Type v) (k : Type u) [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] :
    MvPowerSeries σ (WittVector p k) ⧸ Ideal.span {(p : MvPowerSeries σ (WittVector p k))}
      ≃+* MvPowerSeries σ k := by
  have hker : (RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k)).FG := by
    rw [WittVector.ker_constantCoeff]
    exact Submodule.fg_span_singleton _
  have heq : (RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k)).map
      (MvPowerSeries.C (σ := σ)) = Ideal.span {(p : MvPowerSeries σ (WittVector p k))} := by
    rw [WittVector.ker_constantCoeff, Ideal.map_span, Set.image_singleton, map_natCast]
  exact (Ideal.quotEquivOfEq heq.symm).trans
    (powerSeriesCoefficientQuotientEquiv σ WittVector.constantCoeff
      (WittVector.constantCoeff_surjective p) hker)

/-- Witt係数のmod p同型は、代表元の各係数を定数係数へ送る。 -/
@[simp] theorem wittPowerSeriesModPEquiv_mk (σ : Type v) (k : Type u) [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (φ : MvPowerSeries σ (WittVector p k)) :
    wittPowerSeriesModPEquiv σ k p (Ideal.Quotient.mk _ φ) =
      MvPowerSeries.map WittVector.constantCoeff φ := rfl

/-- Witt冪級数の表示を持つ環のmod p商と、剰余係数の冪級数環の同型。 -/
def wittPresentedModPEquiv (A : Type (max u v)) [CommRing A] (σ : Type v)
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (e : A ≃+* MvPowerSeries σ (WittVector p k)) :
    A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k :=
  (Ideal.quotientEquiv (Ideal.span {(p : A)})
    (Ideal.span {(p : MvPowerSeries σ (WittVector p k))}) e (by
      rw [Ideal.map_span, Set.image_singleton, map_natCast])).trans
    (wittPowerSeriesModPEquiv σ k p)

@[simp] theorem wittPresentedModPEquiv_mk (A : Type (max u v)) [CommRing A] (σ : Type v)
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (e : A ≃+* MvPowerSeries σ (WittVector p k)) (a : A) :
    wittPresentedModPEquiv A σ k p e (Ideal.Quotient.mk _ a) =
      MvPowerSeries.map WittVector.constantCoeff (e a) := rfl

/-- 表示の座標はmod pの同型でも同じ変数へ送られる。 -/
theorem wittPresentedModPEquiv_coordinate (A : Type (max u v)) [CommRing A] (σ : Type v)
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (e : A ≃+* MvPowerSeries σ (WittVector p k)) (a : A) (i : σ)
    (ha : e a = MvPowerSeries.X i) :
    wittPresentedModPEquiv A σ k p e (Ideal.Quotient.mk _ a) = MvPowerSeries.X i := by
  rw [wittPresentedModPEquiv_mk, ha, MvPowerSeries.map_X]

end ModP

end SerrePositivity
