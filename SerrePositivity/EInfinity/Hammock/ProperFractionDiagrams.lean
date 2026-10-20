module

public import SerrePositivity.EInfinity.Hammock.ProperPrecomposition
public import SerrePositivity.EInfinity.Hammock.WordForwardImages
public import SerrePositivity.EInfinity.Hammock.WordPaddingImages

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

variable {F : Word ⥤ SSet.{w}} (hF : ProperDiagram F)

include hF in
lemma ProperDiagram.sandwich (p q : Word) : ProperDiagram (Word.sandwichFunctor p q ⋙ F) :=
  hF.precomp _ (fun f hf => Word.sandwichMap_injective p q f hf)
    (fun f g _ _ => Word.sandwichMap_intersection_range p q f g)

include hF in
lemma ProperDiagram.forwardCore : ProperDiagram (Word.forwardFunctor ⋙ F) :=
  hF.precomp _ (fun f hf => Word.forwardMap_injective f hf)
    (fun f g _ _ => Word.forwardMap_intersection_range f g)

include hF in
lemma ProperDiagram.padding : ProperDiagram (Word.paddingFunctor ⋙ F) :=
  hF.sandwich (Word.single .backward) (Word.single .backward)

include hF in
lemma ProperDiagram.paddedForward :
    ProperDiagram (Word.forwardFunctor ⋙ Word.paddingFunctor ⋙ F) :=
  hF.padding.forwardCore

def paddingDiagramMap (F : Word ⥤ SSet.{w}) : F ⟶ Word.paddingFunctor ⋙ F :=
  Functor.whiskerRight Word.paddingInclusionNat F

lemma paddingDiagramMap_app (F : Word ⥤ SSet.{w}) (a : Word) :
    (paddingDiagramMap F).app a = F.map (Word.paddingInclusionNat.app a) := rfl

def paddedForwardDiagramMap (F : Word ⥤ SSet.{w}) :
    Word.forwardFunctor ⋙ Word.paddingFunctor ⋙ F ⟶ Word.paddingFunctor ⋙ F :=
  Functor.whiskerRight Word.forwardInclusionNat (Word.paddingFunctor ⋙ F)

lemma paddedForwardDiagramMap_app (F : Word ⥤ SSet.{w}) (a : Word) :
    (paddedForwardDiagramMap F).app a =
      F.map (Word.paddingFunctor.map (Word.forwardInclusion a)) := rfl

end SerrePositivity.EInfinity.Hammock
