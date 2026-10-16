module
public import SerrePositivity.DifferentialGraded.Quotient.PrependAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinRightAction

/-! # 有限path連結と先頭Hom作用の結合則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元のHomを先頭へ作用させる操作と有限path連結は結合する。 -/
@[reassoc] lemma appendMap_prepend {S : Set D} (w v : Word S) (x y z t : D) :
    (prependMap A D w x y z ▷ term A D v z t) ≫ appendMap A D w v x z t =
    (α_ (homObject A D x y) (term A D w y z) (term A D v z t)).hom ≫
      (homObject A D x y) ◁ appendMap A D w v y z t ≫ prependMap A D (w ++ v) x y t := by
  cases w with
  | nil => exact prependMap_assoc A D v x y z t
  | cons b w =>
    simpa only [prependMap, appendMap, term_cons, tensorHom_id, List.cons_append] using
      tensorJoin_right_action (homObject A D x y) (homObject A D y b.val)
        (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val z)
        (term A D v z t) (epsilonComplex A ⊗ term A D (w ++ v) b.val t)
        (eComp (Complex A) x y b.val)
        ((α_ (epsilonComplex A) (term A D w b.val z) (term A D v z t)).hom ≫
          (epsilonComplex A) ◁ appendMap A D w v b.val z t)

end SerrePositivity.DifferentialGraded.DGQuotient
