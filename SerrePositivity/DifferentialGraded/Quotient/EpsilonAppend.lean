module
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition
public import SerrePositivity.DifferentialGraded.Quotient.PrependUnit
public import SerrePositivity.DifferentialGraded.Complexes.TensorUnitInsertion

/-! # 単一ε pathを連結したときの単位因子の消去 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma epsilonTerm_append {S : Set D} (b : S) (w : Word S) (y : D) :
    (epsilonTerm A D b ▷ term A D w b.val y) ≫ appendMap A D [b] w b.val b.val y =
    (λ_ (epsilonComplex A ⊗ term A D w b.val y)).inv ≫
      eId (Complex A) b.val ▷ (epsilonComplex A ⊗ term A D w b.val y) := by
  simpa only [epsilonTerm, appendMap, List.nil_append, term_nil] using
    tensorSandwich_append (epsilonComplex A) (homObject A D b.val b.val) (term A D w b.val y)
      (eId (Complex A) b.val) (prependMap A D w b.val b.val y)
      (prependMap_left_unit A D w b.val y)

lemma prependMap_epsilonTerm_append {S : Set D} (b : S) (w : Word S) (x y : D) :
    (homObject A D x b.val) ◁
      ((epsilonTerm A D b ▷ term A D w b.val y) ≫ appendMap A D [b] w b.val b.val y) ≫
      prependMap A D (b :: w) x b.val y = 𝟙 (term A D (b :: w) x y) := by
  rw [epsilonTerm_append]
  simpa only [prependMap, term_cons, tensorHom_id] using
    tensorJoin_right_unit (homObject A D x b.val) (homObject A D b.val b.val)
      (epsilonComplex A ⊗ term A D w b.val y) (eId (Complex A) b.val)
      (eComp (Complex A) x b.val b.val) (e_comp_id (Complex A) x b.val)

end SerrePositivity.DifferentialGraded.DGQuotient
