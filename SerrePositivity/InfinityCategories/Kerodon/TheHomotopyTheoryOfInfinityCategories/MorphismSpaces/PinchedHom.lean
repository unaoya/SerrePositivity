module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedEdges

/-! # dg nerve の右 pinched 写像空間

概要：dg 圏の二対象の間に右 pinched 写像空間を定義し、その頂点を閉零射に同定する。
方針：一般の右 pinched Hom を dg nerve に適用し、端点付き辺の既存の比較を使う。
規約：HA Example 1.3.1.8、Kerodon §4.6.5（Tag 01KW）。使われ方：線形表示と H⁰ との比較の入口。
このファイルの頂点の同値だけでは、全次数の線形表示や Kan 性を主張しない。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：dg 圏の二対象間の右 pinched 写像空間。
方針：dg nerve の対象に対応する零単体を端点として一般の構成を使う。
規約：HA Example 1.3.1.8、Kerodon §4.6.5（Tag 01KW）。使われ方：dg 写像複体からの線形模型との比較先。 -/
def pinchedHom (x y : D) : SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)

namespace PinchedHom

variable {A D} (x y : D)

/-- 概要：右 pinched 写像空間の頂点は x から y への閉次数零元と同値。
方針：端点付き辺との同値を、二次切断の閉零成分の同値に合成する。
規約：HA Example 1.3.1.8、Kerodon §4.6.5（Tag 01KW）。使われ方：π₀ から H⁰ の射への写像。 -/
def vertexCycleEquiv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋0⦌ ≃
    zeroCycles (homObject A D x y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).trans
    { toFun e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e.toTruncated
      invFun f := SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle f)
      left_inv e := SSet.Edge.ext (by
        exact congrArg SSet.Truncated.Edge.edge
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle_edgeCycle e.toTruncated))
      right_inv f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle_edgeOfCycle
        (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) f }

end PinchedHom

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom
