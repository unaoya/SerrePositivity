module

public import SerrePositivity.CommutativeAlgebra.PrescribedParameter
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # 剰余標数pを先頭に置くパラメータ系

標数零のNoether局所整域でpは非零因子となり、剰余標数から極大イデアルに入る。
指定非零因子の一般定理を適用する。完備性・完全剰余体・係数写像は不要。
-/

public section
namespace SerrePositivity
open IsLocalRing

/-- 剰余標数pの標数零局所整域では、(p)による商の次元が一つ下がる。 -/
theorem ringKrullDim_quotient_span_residue_characteristic
    (D : Type*) [CommRing D] [IsNoetherianRing D] [IsLocalRing D] [IsDomain D]
    [CharZero D] (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField D) p]
    {r : ℕ} (hdim : ringKrullDim D = r + 1) :
    ringKrullDim (D ⧸ Ideal.span {(p : D)}) = r := by
  apply ringKrullDim_quotient_eq_of_nonZeroDivisor D (p : D) ?_ ?_ hdim
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  · rw [← residue_eq_zero_iff]
    simp only [map_natCast, CharP.cast_eq_zero]

/-- 次元h>0の混標数局所整域では、pを先頭とするh個のパラメータが存在する。
h=1では残りの列は空となり、(p)自体の根基が極大イデアルになる。 -/
theorem exists_mixedCharacteristic_systemOfParameters
    (D : Type*) [CommRing D] [IsNoetherianRing D] [IsLocalRing D] [IsDomain D]
    [CharZero D] (p : ℕ) [hp : Fact p.Prime] [CharP (ResidueField D) p]
    {h : ℕ} (hdim : ringKrullDim D = h) (hpos : 0 < h) :
    ∃ z : Fin h → D, z ⟨0, hpos⟩ = (p : D) ∧
      (∀ i, z i ∈ maximalIdeal D) ∧ IsSystemOfParameters D z := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  apply exists_systemOfParameters_with_first_nonZeroDivisor D (p : D)
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  · rw [← residue_eq_zero_iff]
    simp only [map_natCast, CharP.cast_eq_zero]
  · simpa only [Nat.cast_succ] using hdim

end SerrePositivity
