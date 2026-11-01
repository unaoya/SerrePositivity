module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardEquivalence
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedDiagram
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeMarkedCategory
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryRelativeForward

/-!
# 元の前向き二列の係数と相対関手による二方向図式

概要：元の相対関手と全ての端点表示を保って切断の各成分を送る。
方針：元の指定部分圏の関手と全係数の元の自然変換を使う。
規約：始点・終点の表示を等式で移し、元の射を保持する。
使われ方：DK9.4・10.3の分解の全相対作用素への自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary SimplicialLocalization

def forwardForwardData (C : RelativeCategory.{u}) (w : Word) (X Y : C.category) :
    TwoSidedDiagram.Data.{u} where
  base := Cat.of (WideSubcategory C.weakEquivalences)
  left := forwardLeftCoefficient C.weakEquivalences w Y
  right := forwardRightCoefficient C.weakEquivalences X

variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def forwardForwardLeftMap : (forwardForwardData C w X Y).left ⟶
    (markedCategoryMap F).op ⋙ (forwardForwardData D w X' Y').left where
  app Z := (Zigzag.Relative.fixedFunctor (w := Word.cons .forward w) F
    (rfl : F.functor.obj Z.unop.obj = F.functor.obj Z.unop.obj) hY).toCatHom
  naturality Z Z' f := by
    apply Cat.Hom.ext
    exact forward_relative_functor F hY f.unop.hom

def forwardForwardRightMap : (forwardForwardData C w X Y).right ⟶
    markedCategoryMap F ⋙ (forwardForwardData D w X' Y').right where
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
  base := markedCategoryMap F
  left := forwardForwardLeftMap w F hY
  right := forwardForwardRightMap w F hX
end SerrePositivity.EInfinity.Hammock.FirstColumn
