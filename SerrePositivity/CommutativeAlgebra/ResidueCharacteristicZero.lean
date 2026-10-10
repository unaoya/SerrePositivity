module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # 剰余標数零の局所環への有理数の埋め込み

剰余体が標数零なら、非零整数の像は剰余体で消えないため局所環の単元である。
整数環の分数体の普遍性によって `ℚ → R` を構成する。
環自体に体の構造や完備性を要求せず、Serre の等標数正値性への接続に使う。
-/

@[expose] public section

namespace SerrePositivity

open IsLocalRing

/-- 剰余標数零の局所環では、非零整数の像は単元である。 -/
theorem isUnit_intCast_of_residueCharZero
    (R : Type*) [CommRing R] [IsLocalRing R] [CharZero (ResidueField R)]
    {n : ℤ} (hn : n ≠ 0) : IsUnit (n : R) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa only [map_intCast, Int.cast_ne_zero] using hn

/-- 剰余標数零の局所環の `ℚ` 代数構造。非零整数の単元性から分数体の写像を作る。 -/
@[instance_reducible]
noncomputable def ratAlgebra_of_residueCharZero
    (R : Type*) [CommRing R] [IsLocalRing R] [CharZero (ResidueField R)] : Algebra ℚ R :=
  (IsLocalization.lift (S := ℚ) (g := Int.castRingHom R) fun n ↦
    isUnit_intCast_of_residueCharZero R (mem_nonZeroDivisors_iff_ne_zero.mp n.property)).toAlgebra

end SerrePositivity
