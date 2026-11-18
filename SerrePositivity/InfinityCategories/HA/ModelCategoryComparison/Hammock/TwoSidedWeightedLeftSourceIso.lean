module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSourceRows

/-!
# 元の重み付き左 bar と反対側の一方向 bar の対角同型

概要：元の重み付き始域は右ラベルの要素圏上の一方向 bar の反転と同型となる。
方針：二重単体的同型の外側をもう一度反転し、二重反転の元の同型で戻す。
規約：両方の単体方向の反転を保持し、元の対角の同じ射を使う。
使われ方：元の重み付き左比較の弱同値性への移送。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource
open _root_.CategoryTheory _root_.Opposite
open _root_.SerrePositivity.SimplicialModel

def diagonalDoubleOpIso (B : SimplicialObject SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj
      (SimplicialObject.opFunctor.obj (B ⋙ SSet.opFunctor)) ≅
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj B).op :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro e
    rfl)

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u)

def spaceIso : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeft.space F S ≅
    ((BarConstruction.functor S.Elementsᵒᵖ).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S ⋙ nerveFunctor)).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso
    ((SimplicialObject.opFunctorCompOpFunctorIso.app
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows (F ⋙ nerveFunctor) (S ⋙ Functor.const SimplexCategoryᵒᵖ))).symm ≪≫
        SimplicialObject.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource.rowsIso F S)) ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource.diagonalDoubleOpIso ((BarConstruction.rows S.Elementsᵒᵖ).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S ⋙ nerveFunctor))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedWeightedLeftSource
