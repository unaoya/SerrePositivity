module

public import SerrePositivity.EInfinity.Hammock.ProperPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardImages
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPaddingImages

/-!
# 分数計算の元の比較図式と proper 性

概要：元の図式の padding と forward 部分語による前合成は proper 性を保つ。
方針：単射と列の像の交わりの保存を、元の語関手に対して証明済みの式で照合する。
規約：比較の成分は元の語の包含の像。成分の弱同値性はここでは主張しない。
使われ方：三本矢から元の全語の余極限への比較。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (hF : ProperDiagram F)

include hF in
lemma ProperDiagram.sandwich (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : ProperDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichFunctor p q ⋙ F) :=
  hF.precomp _ (fun f hf => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichMap_injective p q f hf)
    (fun f g _ _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichMap_intersection_range p q f g)

include hF in
lemma ProperDiagram.forwardCore : ProperDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ F) :=
  hF.precomp _ (fun f hf => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMap_injective f hf)
    (fun f g _ _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMap_intersection_range f g)

include hF in
lemma ProperDiagram.padding : ProperDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F) :=
  hF.sandwich (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)

include hF in
lemma ProperDiagram.paddedForward :
    ProperDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F) :=
  hF.padding.forwardCore

def paddingDiagramMap (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) : F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F :=
  Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingInclusionNat F

lemma paddingDiagramMap_app (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (paddingDiagramMap F).app a = F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingInclusionNat.app a) := rfl

def paddedForwardDiagramMap (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F :=
  Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ F)

lemma paddedForwardDiagramMap_app (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (paddedForwardDiagramMap F).app a =
      F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a)) := rfl

end SerrePositivity.EInfinity.Hammock
