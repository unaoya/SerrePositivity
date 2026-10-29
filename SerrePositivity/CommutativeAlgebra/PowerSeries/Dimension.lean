module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # 冪級数環の次元と正則局所性

概要：Noether 局所環 `R` について `dim R[[X_1, …, X_n]] = dim R + n`。`R` が正則局所なら `R[[X]]` も正則局所。
方針：一変数では `X` が非零因子で `R[[X]]/(X) ≅ R` なので次元が一つ上がる（Mathlib の
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`）。極大イデアルの生成数は
高々一つ増える（`PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem`）ので正則性が保たれる。
有限変数へは `MvPowerSeries.finSuccEquiv` で帰納する。
規約：係数環の整域性・完備性は仮定しない。
使われ方：Cohen–Gabber と Witt の正規化で、`A = k[[X]]` が正則局所で次元が `h` であること。
-/

@[expose] public noncomputable section
namespace SerrePositivity

open IsLocalRing

/-- 一変数冪級数の定数係数の核は(X)。 -/
theorem powerSeries_ker_constantCoeff_single (R : Type*) [CommRing R] :
    RingHom.ker (PowerSeries.constantCoeff (R := R)) = Ideal.span {PowerSeries.X} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

/-- 一変数冪級数をXで割った環は係数環に同型。 -/
noncomputable def powerSeries_quotient_X_equiv (R : Type*) [CommRing R] :
    (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)}) ≃+* R :=
  (Ideal.quotEquivOfEq (powerSeries_ker_constantCoeff_single R).symm).trans
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)

/-- 変数Xは局所係数環の一変数冪級数環の極大イデアルに入る。 -/
theorem powerSeries_X_mem_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- Noether局所係数環の一変数冪級数環の次元はdim R+1。 -/
theorem ringKrullDim_powerSeries (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ringKrullDim (PowerSeries R) = ringKrullDim R + 1 := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (show (PowerSeries.X : PowerSeries R) ∈ nonZeroDivisors (PowerSeries R) from
      MvPowerSeries.X_mem_nonZeroDivisors)
    (powerSeries_X_mem_maximalIdeal R)
  rw [RingEquiv.ringKrullDim (powerSeries_quotient_X_equiv R)] at h
  exact h.symm

/-- 一変数冪級数の極大イデアルの生成数は係数環の生成数+1以下。 -/
theorem spanFinrank_powerSeries_maximalIdeal_le (R : Type*) [CommRing R]
    [IsLocalRing R] :
    (maximalIdeal (PowerSeries R)).spanFinrank ≤ (maximalIdeal R).spanFinrank + 1 := by
  have h := PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem
    (powerSeries_X_mem_maximalIdeal R)
  have he : (maximalIdeal (PowerSeries R)).map (PowerSeries.constantCoeff (R := R)) =
      maximalIdeal R := map_maximalIdeal_of_surjective _ PowerSeries.constantCoeff_surj
  rw [he] at h
  exact h

/-- 正則局所係数環の一変数冪級数環は正則局所環。 -/
theorem isRegularLocalRing_powerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (PowerSeries R) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h := spanFinrank_powerSeries_maximalIdeal_le R
  have hc : ((maximalIdeal (PowerSeries R)).spanFinrank : WithBot ℕ∞) ≤
      (maximalIdeal R).spanFinrank + 1 := by exact_mod_cast h
  rw [IsRegularLocalRing.spanFinrank_maximalIdeal (R := R),
    ← ringKrullDim_powerSeries R] at hc
  exact hc

/-- Fin n変数の冪級数環の次元はdim R+n。 -/
theorem ringKrullDim_mvPowerSeries_fin (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) R) = ringKrullDim R + n := by
  induction n with
  | zero => simpa using RingEquiv.ringKrullDim (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv
  | succ n ih =>
    rw [RingEquiv.ringKrullDim (MvPowerSeries.finSuccEquiv R n).toRingEquiv,
      ringKrullDim_powerSeries, ih, Nat.cast_succ, add_assoc]

/-- 正則局所係数環のFin n変数冪級数環は正則局所環。 -/
theorem isRegularLocalRing_mvPowerSeries_fin (R : Type*) [CommRing R]
    [IsRegularLocalRing R] (n : ℕ) : IsRegularLocalRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).symm.toRingEquiv
  | succ n ih =>
    let : IsRegularLocalRing (MvPowerSeries (Fin n) R) := ih
    let : IsRegularLocalRing (PowerSeries (MvPowerSeries (Fin n) R)) :=
      isRegularLocalRing_powerSeries _
    exact IsRegularLocalRing.of_ringEquiv (MvPowerSeries.finSuccEquiv R n).symm.toRingEquiv

/-- 任意の有限型の変数集合についての次元公式。 -/
theorem ringKrullDim_mvPowerSeries (σ R : Type*) [Fintype σ] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + Fintype.card σ := by
  rw [RingEquiv.ringKrullDim (MvPowerSeries.renameEquiv R (Fintype.equivFin σ)).toRingEquiv]
  exact ringKrullDim_mvPowerSeries_fin R _

/-- 任意の有限変数についての正則局所性。 -/
theorem isRegularLocalRing_mvPowerSeries (σ R : Type*) [Finite σ] [CommRing R]
    [IsRegularLocalRing R] : IsRegularLocalRing (MvPowerSeries σ R) := by
  classical
  let := Fintype.ofFinite σ
  let : IsRegularLocalRing (MvPowerSeries (Fin (Fintype.card σ)) R) :=
    isRegularLocalRing_mvPowerSeries_fin R _
  exact IsRegularLocalRing.of_ringEquiv
    (MvPowerSeries.renameEquiv R (Fintype.equivFin σ)).symm.toRingEquiv


end SerrePositivity
