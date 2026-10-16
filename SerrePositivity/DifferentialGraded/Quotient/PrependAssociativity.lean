module
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinAssociativity

/-! # 有限pathの先頭Hom合成の結合則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の二つのHomを先に合成しても、pathへ順に合成しても一致する。 -/
lemma prependMap_assoc {S : Set D} (w : Word S) (x y z t : D) :
    (eComp (Complex A) x y z ▷ term A D w z t) ≫ prependMap A D w x z t =
    (α_ (homObject A D x y) (homObject A D y z) (term A D w z t)).hom ≫
      (homObject A D x y) ◁ prependMap A D w y z t ≫ prependMap A D w x y t := by
  cases w with
  | nil => exact (e_assoc' (Complex A) x y z t).symm
  | cons b w =>
    simpa only [prependMap, term_cons, tensorHom_id] using
      tensorJoin_assoc (homObject A D x y) (homObject A D y z) (homObject A D z b.val)
        (homObject A D x z) (homObject A D y b.val) (homObject A D x b.val)
        (epsilonComplex A ⊗ term A D w b.val t)
        (eComp (Complex A) x y z) (eComp (Complex A) y z b.val)
        (eComp (Complex A) x z b.val) (eComp (Complex A) x y b.val)
        (e_assoc' (Complex A) x y z b.val).symm

end SerrePositivity.DifferentialGraded.DGQuotient
