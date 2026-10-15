module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftingStep
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerNaturality
public import Mathlib.Order.SuccPred.Nat

/-! # Reedy lifting data below a natural-number degree -/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y} {a : A ⟶ X} {b : B ⟶ Y}

structure LiftBelow (_sq : CommSq a i p b) (n : ℕ) where
  hom : lowerInclusion r n ⋙ B ⟶ lowerInclusion r n ⋙ X
  fac_left : Functor.whiskerLeft (lowerInclusion r n) i ≫ hom =
    Functor.whiskerLeft (lowerInclusion r n) a
  fac_right : hom ≫ Functor.whiskerLeft (lowerInclusion r n) p =
    Functor.whiskerLeft (lowerInclusion r n) b

namespace LiftBelow
variable {r} {sq : CommSq a i p b} {n : ℕ} (l : LiftBelow r sq n)

abbrev restrictAt (j : J) (hj : r.deg j ≤ n) :
    lowerInclusion r (r.deg j) ⋙ B ⟶ lowerInclusion r (r.deg j) ⋙ X :=
  Functor.whiskerLeft (lowerMap r hj) l.hom

lemma restrictAt_fac_left (j : J) (hj : r.deg j ≤ n) :
    Functor.whiskerLeft (lowerInclusion r (r.deg j)) i ≫ l.restrictAt j hj =
      Functor.whiskerLeft (lowerInclusion r (r.deg j)) a := by
  apply NatTrans.ext
  funext k
  exact congr_app l.fac_left ⟨k.obj, lt_of_lt_of_le k.property hj⟩

lemma restrictAt_fac_right (j : J) (hj : r.deg j ≤ n) :
    l.restrictAt j hj ≫ Functor.whiskerLeft (lowerInclusion r (r.deg j)) p =
      Functor.whiskerLeft (lowerInclusion r (r.deg j)) b := by
  apply NatTrans.ext
  funext k
  exact congr_app l.fac_right ⟨k.obj, lt_of_lt_of_le k.property hj⟩

variable (r) (sq) in
/-- Before degree zero there are no components to choose. -/
def zero : LiftBelow r sq 0 where
  hom :=
    { app j := (Nat.not_lt_zero _ j.property).elim
      naturality j _ _ := (Nat.not_lt_zero _ j.property).elim }
  fac_left := by
    apply NatTrans.ext
    funext j
    exact (Nat.not_lt_zero _ j.property).elim
  fac_right := by
    apply NatTrans.ext
    funext j
    exact (Nat.not_lt_zero _ j.property).elim

end LiftBelow
end SerrePositivity.Reedy
