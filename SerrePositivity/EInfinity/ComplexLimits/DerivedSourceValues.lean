module

public import SerrePositivity.EInfinity.ComplexLimits.KProjectiveDerivedSource
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionValue

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexOrdinaryDerivedSource_vertex_eq (X : Complex A) :
    (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A X) := by
  have hx : (nerveMap (complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
    rfl
  change (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
    ((nerveMap (complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) = _
  rw [hx, complexSemifreeResolutionInfinity_vertex]

lemma kProjectiveDerivedSource_vertex_eq (X : KProjectiveComplex A) :
    (kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (complexSemifreeResolutionValue A X.val) := by
  change (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.val) = _
  exact complexSemifreeResolutionInfinity_vertex A X.val

end SerrePositivity.EInfinity.ComplexLimits
