module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnBackwardBackwardEquivalence
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedDiagram
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeMarkedCategory
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryRelativeBackward

/-!
# 元の後向き二列の底と両係数の相対比較

概要：元の指定部分圏の Hom と残りの語の共変係数を保つ。
方針：同じ元の切断関手と全相対関手を使う。
規約：元の全対象・全縦射と端点表示を保持する。
使われ方：DK9.4・10.3の後向き二列の自然な分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary SimplicialLocalization

def backwardBackwardData (C : RelativeCategory.{u}) (w : Word) (X Y : C.category) :
    TwoSidedDiagram.Data.{u} where
  base := Cat.of (WideSubcategory C.weakEquivalences)
  left := backwardLeftCoefficient C.weakEquivalences X
  right := backwardRightCoefficient C.weakEquivalences w Y

variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def backwardBackwardLeftMap : (backwardBackwardData C w X Y).left ⟶
    (markedCategoryMap F).op ⋙ (backwardBackwardData D w X' Y').left where
  app Z := (Discrete.functor (fun e : Z.unop ⟶ (⟨X⟩ : WideSubcategory C.weakEquivalences) =>
    Discrete.mk ((markedCategoryMap F).map e ≫ eqToHom
      (congrArg (fun T => (⟨T⟩ : WideSubcategory D.weakEquivalences)) hX)))).toCatHom
  naturality Z Z' f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun e => Discrete.ext ?_) ?_
    · change ((markedCategoryMap F).map (f.unop ≫ e.as)) ≫ eqToHom _ =
        (markedCategoryMap F).map f.unop ≫ ((markedCategoryMap F).map e.as ≫ eqToHom _)
      simp only [Functor.map_comp, Category.assoc]
    · intro e e' k
      exact @Discrete.hom_eq ((⟨F.functor.obj Z'.unop.obj⟩ : WideSubcategory
        D.weakEquivalences) ⟶ ⟨X'⟩) _ _ _ _

def backwardBackwardRightMap : (backwardBackwardData C w X Y).right ⟶
    markedCategoryMap F ⋙ (backwardBackwardData D w X' Y').right where
  app Z := (Zigzag.Relative.fixedFunctor (w := Word.cons .backward w) F
    (rfl : F.functor.obj Z.obj = F.functor.obj Z.obj) hY).toCatHom
  naturality Z Z' f := by
    apply Cat.Hom.ext
    exact backward_relative_functor F hY f.hom f.property

def backwardBackwardDataMap : backwardBackwardData C w X Y ⟶ backwardBackwardData D w X' Y' where
  base := markedCategoryMap F
  left := backwardBackwardLeftMap w F hX
  right := backwardBackwardRightMap w F hY
end SerrePositivity.EInfinity.Hammock.FirstColumn
