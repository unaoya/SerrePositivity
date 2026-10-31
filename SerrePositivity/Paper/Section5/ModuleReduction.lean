module

public import SerrePositivity.Paper.Section5.PrimeReduction
public import SerrePositivity.IntersectionMultiplicity.Additivity

/-! # 完備・代数閉剰余体の場合の有限生成加群の正値性

素イデアル商の核心定理に零次元の境界計算と両変数のデヴィサージュを適用する。
一般の正則局所環からの完備化・剰余体変更と、剰余標数零の場合はここには含まない。
-/

public section

universe u

namespace SerrePositivity.Section5

open IsLocalRing TensorProduct

/-- 剰余標数が正の完備正則局所環で剰余体が代数閉なら、任意の有限生成加群について正値性が成り立つ。
素イデアル商へのデヴィサージュを内部で行い、正次元の仮定は要求しない。
核の場合と同じ引用入力、および既存の交点消滅定理に依存する。 -/
theorem positivity_of_complete_algClosed
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N :=
  chi_pos_of_prime_quotients (chi_prime_pos_of_complete_algClosed R p) M N hfin hdim

end SerrePositivity.Section5
