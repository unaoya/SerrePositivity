module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeUpperOriginal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeLowerOriginal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 元の要素図式の四列比較を全 graph と余極限へ移す

概要：元の Hom 宇宙の異なる要素図式の全射列を同じ graph へ送る。
方針：全語の標準射の自然性と元の連結の式を使う。
規約：元の全単体・全作用素・元の前合成を保持する。
使われ方：始域比較のホモトピーを元の余極限へ渡す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {I : Type v} [Category.{0} I] {B E X' X Y : C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}

def diagramGraphMap (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w B E) : nerve (ULiftHom.{max u v} I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w B E where
  app _ := ↾fun σ => σ ⋙ ULiftHom.down.{0, v, max u v} ⋙ F
  naturality _ _ _ := rfl

def diagramColimitMap (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w B E) :
    nerve (ULiftHom.{max u v} I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W B E :=
  diagramGraphMap W F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W B E w

lemma diagramColimitMap_wordAction (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w B E) {w' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : w ⟶ w') :
    diagramColimitMap W (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) = diagramColimitMap W F := by
  have h : diagramGraphMap W (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) =
      diagramGraphMap W F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W B E).map f := rfl
  unfold diagramColimitMap
  rw [h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality]

lemma diagramColimitMap_precompose (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y) (f : X' ⟶ X) :
    diagramColimitMap W
        (((Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f)).prod' F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) =
      diagramColimitMap W F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let Γ := σ ⋙ ULiftHom.down.{0, v, max u v} ⋙ F
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X' Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.preWord).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n).prod' Γ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X' X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W f n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word).app n Γ)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions W X' X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n) Γ).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
