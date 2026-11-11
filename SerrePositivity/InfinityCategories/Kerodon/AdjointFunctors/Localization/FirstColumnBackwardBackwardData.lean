module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeMarkedCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryRelativeBackward

/-!
# 元の後向き二列の底と両係数の相対比較

概要：元の指定部分圏の Hom と残りの語の共変係数を保つ。
方針：同じ元の切断関手と全相対関手を使う。
規約：元の全対象・全縦射と端点表示を保持する。
使われ方：DK9.4・10.3の後向き二列の自然な分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary

def backwardBackwardData (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} where
  base := Cat.of (WideSubcategory C.weakEquivalences)
  left := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardLeftCoefficient C.weakEquivalences X
  right := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardRightCoefficient C.weakEquivalences w Y

variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def backwardBackwardLeftMap : (backwardBackwardData C w X Y).left ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).op ⋙ (backwardBackwardData D w X' Y').left where
  app Z := (Discrete.functor (fun e : Z.unop ⟶ (⟨X⟩ : WideSubcategory C.weakEquivalences) =>
    Discrete.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).map e ≫ eqToHom
      (congrArg (fun T => (⟨T⟩ : WideSubcategory D.weakEquivalences)) hX)))).toCatHom
  naturality Z Z' f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun e => Discrete.ext ?_) ?_
    · change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).map (f.unop ≫ e.as)) ≫ eqToHom _ =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).map f.unop ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).map e.as ≫ eqToHom _)
      simp only [Functor.map_comp, Category.assoc]
    · intro e e' k
      exact @Discrete.hom_eq ((⟨F.functor.obj Z'.unop.obj⟩ : WideSubcategory
        D.weakEquivalences) ⟶ ⟨X'⟩) _ _ _ _

def backwardBackwardRightMap : (backwardBackwardData C w X Y).right ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F ⋙ (backwardBackwardData D w X' Y').right where
  app Z := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) F
    (rfl : F.functor.obj Z.obj = F.functor.obj Z.obj) hY).toCatHom
  naturality Z Z' f := by
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_relative_functor F hY f.hom f.property

def backwardBackwardDataMap : backwardBackwardData C w X Y ⟶ backwardBackwardData D w X' Y' where
  base := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F
  left := backwardBackwardLeftMap w F hX
  right := backwardBackwardRightMap w F hY
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
