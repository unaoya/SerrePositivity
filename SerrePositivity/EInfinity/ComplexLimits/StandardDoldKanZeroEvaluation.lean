module

public import SerrePositivity.EInfinity.ComplexLimits.DoldKanZeroAdjunction

/-!
# 元の標準 DK Hom 同型の零次数評価

概要：同じ標準 DK 同型の零次数像を、元の正規化同型の零次数で計算する。
方針：元の同型が同じ DK 随伴の Hom 像であることを使う。
規約：standardDoldKanModuleIso と standardNormalizationIso を保つ。
使われ方：正規化 frame の零次数像と元の閉辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

lemma standardDoldKanModuleIso_zero_eval (x y : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x y).hom.app (Opposite.op ⦋0⦌) ≫
      (gammaDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y)).hom =
    (mooreDegreeZeroIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom.f 0 :=
  doldKanAdjunction_zero_eval (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizationIso (R := R) x y).hom

end SerrePositivity.EInfinity.ComplexLimits
