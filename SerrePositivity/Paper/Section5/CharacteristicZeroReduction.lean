module

public import SerrePositivity.Inputs.SerrePositivity
public import SerrePositivity.CommutativeAlgebra.ResidueCharacteristicZero

/-! # 剰余標数零の場合の Serre の定理への帰着

剰余標数零の局所環には `ℚ` の作用がある。これを構成して、
体を含む正則局所環に対する Serre の正値性を適用する。
Serre の定理だけを名前付きの引用として残し、この接続には `sorry` を用いない。
-/

public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 剰余標数零の場合の正値性。`ℚ` 代数構造を作り、Serre の引用定理を適用する。 -/
theorem positivity_of_residueCharZero
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  let := ratAlgebra_of_residueCharZero R
  exact Inputs.serrePositivity_of_field ℚ R M N hfin hdim

end SerrePositivity.Section5
