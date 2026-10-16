module
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinUnit

/-! # 有限pathの先頭Hom合成の左単位則 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

@[reassoc] lemma prependMap_left_unit {S : Set D} (w : Word S) (x y : D) :
    (λ_ (term A D w x y)).inv ≫ eId (Complex A) x ▷ term A D w x y ≫
      prependMap A D w x x y = 𝟙 (term A D w x y) := by
  cases w with
  | nil => exact e_id_comp (Complex A) x y
  | cons b w =>
    simpa only [prependMap, term_cons, tensorHom_id] using
      tensorJoin_left_unit (homObject A D x x) (homObject A D x b.val)
        (epsilonComplex A ⊗ term A D w b.val y) (eId (Complex A) x)
        (eComp (Complex A) x x b.val) (e_id_comp (Complex A) x b.val)

end SerrePositivity.DifferentialGraded.DGQuotient
