module

public import SerrePositivity.EInfinity.Hammock.CoefficientProductRelative
public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardForwardCatIso
public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardData
public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardData

/-!
# 元の混合二方向の底と両係数の相対比較

概要：元の係数積と全相対作用素を保持する。
方針：両係数の元の写像と切断の全成分を組にする。
規約：同じ元の graph と augmentation を使う。
使われ方：DK10.3の混合二方向の自然な分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization Zigzag.FirstBoundary
def backwardForwardData (C : RelativeCategory.{u}) (w : Word) (X Y : C.category) :
    TwoSidedDiagram.Data.{u} where
  base := Cat.of (WideSubcategory C.weakEquivalences)
  left := backwardForwardLeftCoefficient C.weakEquivalences w X Y
  right := CoefficientProduct.point
variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def backwardForwardDataMap : backwardForwardData C w X Y ⟶ backwardForwardData D w X' Y' where
  base := markedCategoryMap F
  left := CoefficientProduct.change (markedCategoryMap F).op
    (backwardBackwardLeftMap (Y := Y) (Y' := Y') w F hX)
    (forwardForwardLeftMap (X := X) (X' := X') w F hY)
  right := CoefficientProduct.pointMap (markedCategoryMap F)
end SerrePositivity.EInfinity.Hammock.FirstColumn
