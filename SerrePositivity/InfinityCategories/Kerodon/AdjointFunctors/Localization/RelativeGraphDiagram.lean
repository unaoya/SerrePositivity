module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 相対関手による元の全語の hammock 図式の比較

概要：同じ元の相対関手から、全語の圏値・単体集合値の図式の自然変換を構成する。
方針：元の WordAction の厳密な関手の等式を nerve へ移す。
規約：ここでは両圏の対象・Hom の宇宙を揃える。自由相対解像も同じ宇宙にある。
使われ方：自由解像の augmentation による hammock の二重単体的比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (X Y : C)

def categoryDiagramMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.categoryDiagram W X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.categoryDiagram V (F.functor.obj X) (F.functor.obj Y) where
  app w := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := w) (X := X) (Y := Y) F).toCatHom
  naturality _ _ f := by
    apply Cat.Hom.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_functor_eq F f).symm

def graphDiagramMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram V (F.functor.obj X) (F.functor.obj Y) :=
  Functor.whiskerRight (categoryDiagramMap F X Y) nerveFunctor

lemma graphDiagramMap_app (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : (graphDiagramMap F X Y).app w =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := w) (X := X) (Y := Y) F) := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
