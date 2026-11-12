module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramDiagonalArrow
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramDiagonalOrder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QuasicategoryDiagramRealization

/-!
概要：同じ自然変換の辺の全パラメーターでの対角実現は、元の prism の同じ単体。
方針：同じ二点図式の通常の対角関手と、その coherent 表示を使う。
規約：底と区間の全次数の単体を同時に保持する。
使われ方：結合同型の分類像と既存の結合区間族を厳密に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 自然変換の同じ辺を任意の区間の射列で引き戻して実現すると、元の prism の単体になる。 -/
lemma quasicategoryDiagramDiagonalSimplex_naturalPrism
    {C : Type u} [Category.{u} C] {F G : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C}
    (η : F.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget ⟶ G.val ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget)
    {n : ℕ} (σ : (nerve C) _⦋n⦌) (τ : Fin (n + 1) ⥤ Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.quasicategoryDiagramDiagonalSimplex σ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramCategory C)).app (Opposite.op ⦋n⦌)
        (τ ⋙ ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramHom η))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatDiagramCoherentNerve
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramQCatTransformation η))).app (Opposite.op ⦋n⦌)
        (ULift.up (τ.prod' σ)) := by
  let B : ULift.{u} (Fin (n + 1)) ⥤ Fin 2 × C :=
    (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙
      τ.prod' σ
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalQuasicategoryDiagramEvaluation (B ⋙ CategoryTheory.Prod.snd (Fin 2) C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram (B ⋙ CategoryTheory.Prod.fst (Fin 2) C ⋙
        ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramHom η))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram
      (B ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.qCatDiagramArrow (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramQCatTransformation η))
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.diagonalQuasicategoryDiagramEvaluation_order,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramDiagonalFunctor_precomp, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryDiagramDiagonalFunctor_arrow]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
