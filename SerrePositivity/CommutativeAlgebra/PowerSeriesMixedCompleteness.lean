module

public import SerrePositivity.CommutativeAlgebra.PowerSeriesCoefficientCompleteness
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.FieldTheory.Perfect

/-! # 係数イデアルと変数を合わせた冪級数の完備性

係数拡張と変数イデアルの二つの実際の完備性を、和の完備性の一般定理へ接続する。
Witt係数では(p,X)進完備性を供給する。
-/

public section
namespace SerrePositivity

/-- 形式変数は局所係数環の冪級数環の極大イデアルに入る。 -/
theorem powerSeries_variables_le_maximalIdeal
    (σ R : Type*) [CommRing R] [IsLocalRing R] :
    Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) ≤
      IsLocalRing.maximalIdeal (MvPowerSeries σ R) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change MvPowerSeries.X i ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ R)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp

/-- 完備Noether局所係数環の有限変数冪級数は、係数イデアルと全変数の和について完備。 -/
theorem isAdicComplete_powerSeries_coefficients_sup_variables
    (σ R : Type*) [Finite σ] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete (I.map MvPowerSeries.C ⊔
      Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) (MvPowerSeries σ R) := by
  let : IsAdicComplete (I.map (MvPowerSeries.C (σ := σ))) (MvPowerSeries σ R) :=
    isAdicComplete_powerSeries_coefficients I (IsNoetherian.noetherian I)
  exact isAdicComplete_sup_of_noetherian_local _ _ (powerSeries_variables_le_maximalIdeal σ R)

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

end SerrePositivity
