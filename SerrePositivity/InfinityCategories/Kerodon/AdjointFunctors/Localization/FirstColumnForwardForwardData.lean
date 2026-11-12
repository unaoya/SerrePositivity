module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeMarkedCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryRelativeForward

/-!
# 元の前向き二列の係数と相対関手による二方向図式

概要：元の相対関手と全ての端点表示を保って切断の各成分を送る。
方針：元の指定部分圏の関手と全係数の元の自然変換を使う。
規約：始点・終点の表示を等式で移し、元の射を保持する。
使われ方：DK9.4・10.3の分解の全相対作用素への自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary

def forwardForwardData (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} where
  base := Cat.of (WideSubcategory C.weakEquivalences)
  left := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardLeftCoefficient C.weakEquivalences w Y
  right := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardRightCoefficient C.weakEquivalences X

variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def forwardForwardLeftMap : (forwardForwardData C w X Y).left ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).op ⋙ (forwardForwardData D w X' Y').left where
  app Z := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) F
    (rfl : F.functor.obj Z.unop.obj = F.functor.obj Z.unop.obj) hY).toCatHom
  naturality Z Z' f := by
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_relative_functor F hY f.unop.hom

def forwardForwardRightMap : (forwardForwardData C w X Y).right ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F ⋙ (forwardForwardData D w X' Y').right where
  app Z := (Discrete.functor (fun e : X ⟶ Z.obj =>
    Discrete.mk (eqToHom hX.symm ≫ F.functor.map e))).toCatHom
  naturality Z Z' f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun e => Discrete.ext ?_) ?_
    · change eqToHom hX.symm ≫ F.functor.map (e.as ≫ f.hom) =
        (eqToHom hX.symm ≫ F.functor.map e.as) ≫ F.functor.map f.hom
      simp only [Functor.map_comp, Category.assoc]
    · intro e e' k
      have : Subsingleton ((Discrete.mk (eqToHom hX.symm ≫ F.functor.map (e.as ≫ f.hom))) ⟶
          Discrete.mk (eqToHom hX.symm ≫ F.functor.map (e'.as ≫ f.hom))) := inferInstance
      exact this.elim _ _

def forwardForwardDataMap : forwardForwardData C w X Y ⟶ forwardForwardData D w X' Y' where
  base := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F
  left := forwardForwardLeftMap w F hY
  right := forwardForwardRightMap w F hX
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
