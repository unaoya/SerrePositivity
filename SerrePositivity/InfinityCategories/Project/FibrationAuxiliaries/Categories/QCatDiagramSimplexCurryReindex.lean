module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramSimplexCurry

/-!
概要：同じ単体と底の積の curry は、底の関手による同じ制限と厳密に可換。
方針：各次数の元の二変数の族に同じ底の関手を作用させる。
規約：元の Hom と元のパラメーターの制限を保持する。
使われ方：比較三角形の最初の面を、既存の底変換比較の同じ底制限へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ curry の底変換は、元の積上の底変換そのもの。 -/
lemma qCatDiagramSimplexCurry_reindex (n : ℕ) {C D : Type u} [Category.{u} C] [Category.{u} D]
    (k : D ⥤ C) :
    (pre ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap ((Functor.id (Fin (n + 1))).prod k)))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} ≫
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramSimplexCurry n D =
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramSimplexCurry n C ≫ (ihom (Δ[n] : SSet.{u + 1})).map
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}) := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro r α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
