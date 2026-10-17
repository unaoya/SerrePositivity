module

public import SerrePositivity.IntersectionMultiplicity.EqualCharZeroPositivity

/-! # 剰余標数零の場合の正値性

剰余標数零の正則局所環では、Serre の対角線論法で正値性を示す
（`IntersectionMultiplicity/EqualCharZeroPositivity.lean`）。
完備化、標数零の係数体と Cohen 同型、素イデアル商へのデヴィサージュ、
冪級数環での対角線の商の Koszul 重複度による。
Serre の等標数正値性の一般形の引用（旧 `Inputs.serrePositivity_of_field`、削除済み）は使わない。
デヴィサージュは交点重複度の消滅定理の引用に依存する。
-/

public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 剰余標数零の場合の正値性。対角線論法による証明済みの定理を適用する。 -/
theorem positivity_of_residueCharZero
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N :=
  chi_pos_of_residueCharZero R M N hfin hdim

end SerrePositivity.Section5
