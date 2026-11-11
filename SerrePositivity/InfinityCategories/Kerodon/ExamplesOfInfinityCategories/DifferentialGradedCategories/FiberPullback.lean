module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberBoundaryJoinFaces

/-! # 標準 fiber の錐は ∞ 引き戻し

概要：非有界複体の標準 fiber の錐は dg nerve の cospan の極限錐である。
方針：slice の任意の正次元境界を二セルの有限成分で直接充填し、curry して終対象性を得る。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：導来 ∞ 圏の標準引き戻し。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：標準 fiber の錐は複体の dg nerve の cospan の極限錐である。
方針：最後の頂点が標準錐である slice 境界に明示的な左右の単体を作り、貼合せた join 写像を curry する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：標準 fiber 四角形の ∞ 引き戻し性。 -/
lemma standardFiberCone_isLimit (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h) := by
  intro n b hb
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberBoundaryJoinFiller g h b hb
  have hfaces := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberBoundaryJoinFiller_faces g h b hb
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.joinBoundaryFaces_fixed _ b F hfaces), ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sliceOverCurry_boundary_of_joinFaces _ b F hfaces

/-- 概要：標準 mapping cone の −1 シフトによる fiber 四角形は dg nerve の ∞ 引き戻し四角形である。
方針：対応する標準錐の slice の終対象性を引き戻し四角形の定義へ戻す。
規約：HTT §1.2.13、HA §1.3.1。使われ方：錐で閉じた充満 dg 部分圏と擬同型判定への入力。 -/
lemma standardFiberSquare_isPullback (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h) :=
  standardFiberCone_isLimit g h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
