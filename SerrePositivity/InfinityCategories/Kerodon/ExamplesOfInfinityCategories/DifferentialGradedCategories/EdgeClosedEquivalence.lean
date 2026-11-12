module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TruncatedTriangles
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
dg nerve の辺と閉零圏の射の同値。Kerodon 2.5.4.1（Tag 00PZ）。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open CategoryTheory.SimplicialObject.Truncated
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：零単体は閉零圏の対象を定める。
方針：唯一の頂点の対象を既存の豊穣忘却の対象に移す。
規約：HA Example 1.3.1.8。使われ方：H⁰ への比較関手の対象写像。 -/
def vertexClosed (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂) : ClosedCategory A D :=
  ForgetEnrichment.of (Complex A) (x.obj 0)

/-- 概要：端点付きの辺と既存の閉零圏の射は同値。
方針：辺と閉零元の同値を、単位複体からの射との同値に合成する。
規約：HA Example 1.3.1.8。使われ方：射の商の同値の構成。 -/
@[kerodon 00PZ]
def edgeClosedEquiv (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) _⦋0⦌₂) :
    SSet.Truncated.Edge x y ≃ (vertexClosed x ⟶ vertexClosed y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycleEquiv x y).trans (closedHomEquiv A D _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
