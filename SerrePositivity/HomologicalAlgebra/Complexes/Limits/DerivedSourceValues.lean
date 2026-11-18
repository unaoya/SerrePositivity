module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.KProjectiveDerivedSource
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SemifreeResolutionValue

/-!
# 元の通常導来源と K-projective 導来源の同じ値

概要：二つの実導来源の頂点は同じ半自由出力分解の標準頂点である。
方針：元の閉 nerve の零単体を計算し、既存の実分解の頂点公式を使う。
規約：対象の同型でなく元の値の等式。
使われ方：正規化 Hom 比較の端点を元の通常導来源へ厳密に合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma complexOrdinaryDerivedSource_vertex_eq (X : Complex A) :
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A X) := by
  have hx : (nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
    rfl
  change (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
    ((nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) = _
  rw [hx, _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity_vertex]

lemma kProjectiveDerivedSource_vertex_eq (X : _root_.SerrePositivity.ComplexLimits.KProjectiveComplex A) :
    (_root_.SerrePositivity.ComplexLimits.kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A X.val) := by
  change (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val) = _
  exact _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity_vertex A X.val

end SerrePositivity.ComplexLimits
