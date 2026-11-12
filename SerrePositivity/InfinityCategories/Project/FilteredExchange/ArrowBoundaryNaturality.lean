module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundaryEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram

/-!
概要：二点の関手空間の評価同型は後合成と定値図式を保つ。
方針：二つの固定頂点の評価を各次数で計算する。
規約：元の始点・終点の順を維持する。
使われ方：定値底の境界関手を同じ fiber の二対象の組として表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：二点の関手の評価は元の射による後合成と厳密に可換。
方針：各次数で二つの値を写す式を計算する。
規約：任意の射。使われ方：境界の関手全空間の底変換。 -/
lemma arrowBoundaryEvaluation_naturality {E B : SSet.{u}} (p : E ⟶ B) :
    (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary).map p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation B =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation E ≫ (p ⊗ₘ p) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：定値図式の固定頂点での評価は恒等射。
方針：第二射影の curry と指定頂点の評価の式を使う。
規約：形状と標的は任意。使われ方：定値図式の境界の対角表示。 -/
lemma constantDiagram_evaluate {K X : SSet.{u}} (v : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v = 𝟙 X := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, lift_snd]

/-- 概要：二点上の定値図式は元の二項対角に一致。
方針：両頂点の定値図式の評価式を使う。
規約：元の二つの恒等射の組。使われ方：同じ底を共有する二対象の引き戻し表示。 -/
lemma constantDiagram_arrowBoundaryEvaluation (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation B = lift (𝟙 B) (𝟙 B) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation, Category.assoc, lift_fst, lift_fst, constantDiagram_evaluate]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation, Category.assoc, lift_snd, lift_snd, constantDiagram_evaluate]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
