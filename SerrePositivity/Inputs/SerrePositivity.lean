module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Module

/-! # Serre の等標数正値性（文献からの引用）

体を含む正則局所環における交点重複度の正値性を、名前付きの未証明定理として引用する。
出典は Serre, *Local Algebra*, Chapter V, Theorem 1 の等標数の場合
（https://doi.org/10.1007/978-3-662-04203-8）。論文 Lemma 5.1 で使う古典的な入力である。

剰余標数零から体の作用を構成する部分はこの入力に含めず、
`CommutativeAlgebra/ResidueCharacteristicZero.lean` と
`Paper/Section5/CharacteristicZeroReduction.lean` で証明する。
-/

public section

universe u

namespace SerrePositivity.Inputs

open TensorProduct

/-- Serre の正値性定理の等標数の場合（引用、未証明）。
体 `k` 上の正則局所環で、非零有限生成加群のテンソル積が有限長、
かつ台の次元の和が環の次元に等しければ、交点重複度は正である。 -/
theorem serrePositivity_of_field (k : Type*) [Field k]
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [Algebra k R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  sorry

end SerrePositivity.Inputs
