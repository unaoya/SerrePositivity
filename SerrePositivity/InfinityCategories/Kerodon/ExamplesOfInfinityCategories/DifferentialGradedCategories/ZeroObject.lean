module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroInitial

/-! # 複体 dg nerve の零頂点

概要：零複体の頂点は始対象かつ終対象である。
方針：一般の零対象に対する両方向の直接の境界充填を零複体に適用する。
規約：HTT Definition 1.2.12.3 とその双対。使われ方：N7b、fiber と有限極限の基礎。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject

variable (A : Type u) [CommRing A]

/-- 概要：零複体の頂点は複体 dg nerve の終対象。
方針：零複体が零対象であることに直接の境界充填を適用する。
規約：HTT Definition 1.2.12.3。使われ方：N7b、空図式の極限。 -/
lemma isTerminalVertex_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (0 : Complex A)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_isZero _ (Limits.isZero_zero _)

/-- 概要：零複体の頂点は複体 dg nerve の始対象。
方針：零複体が零対象であることに直接の境界充填の双対を適用する。
規約：HTT Definition 1.2.12.3 の双対。使われ方：N7b、空図式の余極限。 -/
lemma isInitialVertex_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (0 : Complex A)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_isZero _ (Limits.isZero_zero _)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
