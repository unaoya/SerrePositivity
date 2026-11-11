module

public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

/-!
# 元の通常導来源と全複体分解関手の頂点の厳密な照合

概要：元の通常複体 nerve の頂点を同じ全複体 dg nerve の頂点へ戻す。
方針：元の閉零圏包含の零単体を計算し、同じ分解関手で送る。
規約：同じ複体の値の等式だけで輸送する。
使われ方：元の自由単位の辺の像を既存の導来単位成分へ照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexClosedNerve_vertex (X : Complex A) :
    (nerveMap (complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion A (Complex A)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
  rfl

lemma complexOrdinaryAmbient_vertex (X : Complex A) :
    (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
      (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) :=
  congrArg ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌))
    (complexClosedNerve_vertex A X)

def complexOrdinaryAmbientVertexIso (X : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      ((complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) :=
  eqToIso (congrArg HomotopyCategory.mk (complexOrdinaryAmbient_vertex A X))

end SerrePositivity.EInfinity.ComplexLimits
