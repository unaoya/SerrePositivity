module
public import SerrePositivity.InfinityCategories.PinchedHom.Edges
public import SerrePositivity.InfinityCategories.DGNerve.TruncatedEdges

/-! # dg nerve の右 pinched 写像空間

概要：dg 圏の二対象の間に右 pinched 写像空間を定義し、その頂点を閉零射に同定する。
方針：一般の右 pinched Hom を dg nerve に適用し、端点付き辺の既存の比較を使う。
規約：HA Example 1.3.1.8、Kerodon §4.6.5。使われ方：線形表示と H⁰ との比較の入口。
このファイルの頂点の同値だけでは、全次数の線形表示や Kan 性を主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory DifferentialGraded
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：dg 圏の二対象間の右 pinched 写像空間。
方針：dg nerve の対象に対応する零単体を端点として一般の構成を使う。
規約：HA Example 1.3.1.8、Kerodon §4.6.5。使われ方：dg 写像複体からの線形模型との比較先。 -/
def pinchedHom (x y : D) : SSet.{max u v} :=
  InfinityCategories.pinchedHom (X := dgNerve A D) (Simplex.vertex x) (Simplex.vertex y)

namespace PinchedHom

variable {A D} (x y : D)

/-- 概要：右 pinched 写像空間の頂点は x から y への閉次数零元と同値。
方針：端点付き辺との同値を、二次切断の閉零成分の同値に合成する。
規約：HA Example 1.3.1.8、Kerodon §4.6.5。使われ方：π₀ から H⁰ の射への写像。 -/
def vertexCycleEquiv : (DGNerve.pinchedHom A D x y) _⦋0⦌ ≃
    zeroCycles (homObject A D x y) :=
  (InfinityCategories.PinchedHom.vertexEquiv (X := dgNerve A D)
    (Simplex.vertex x) (Simplex.vertex y)).trans
    { toFun e := HomotopyComparison.edgeCycle e.toTruncated
      invFun f := SSet.Edge.ofTruncated (HomotopyComparison.edgeOfCycle f)
      left_inv e := SSet.Edge.ext (by
        exact congrArg SSet.Truncated.Edge.edge
          (HomotopyComparison.edgeOfCycle_edgeCycle e.toTruncated))
      right_inv f := HomotopyComparison.edgeCycle_edgeOfCycle
        (x := Simplex.vertex x) (y := Simplex.vertex y) f }

end PinchedHom

end SerrePositivity.InfinityCategories.DGNerve
