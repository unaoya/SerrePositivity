module

public import SerrePositivity.InfinityCategories.F1.Yoneda.CovariantRepresentableInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafValues
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence

/-!
概要：二重反転を明示した共変表現可能関手の値を、元の C の写像空間と比較する。
方針：反転した C の表現可能前層の値から左写像空間を経て元の右模型へ戻す。
規約：始点・終点の順序を保持し、Kan 反転は同値として扱う。
使われ方：F1-5 の共変関手が Hom(x,−) を表すことの値での確認。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 共変表現可能関手の指定対象での値は、元の同じ対象対の標準写像空間と同値。 -/
def covariantRepresentableValueEquivalence {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    QCatEquivalence
      (spaceInfinityObject ((covariantRepresentableInfinity x).app (Opposite.op ⦋0⦌)
        (ULift.up y))).obj (pinchedHom x y) :=
  (representablePresheafValueEquivalence (C := C.op)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)).trans
      ((kanOppositeEdgewiseEquivalence (pinchedHom (X := C.op)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x))).symm.trans
          (pinchedHomLeftRightEquivalence x y))

end SerrePositivity.InfinityCategories
