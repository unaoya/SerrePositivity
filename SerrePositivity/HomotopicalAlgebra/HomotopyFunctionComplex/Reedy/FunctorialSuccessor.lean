module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialDegreeStep
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationSequence

/-! # Successors of functorial degreewise factorization families

The restriction comparison is natural in the original input arrow and
commutes with both factor transformations. Evaluating the successor
recovers the already constructed ordinary one-object successor.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]

abbrev restrictionBetween {n m : ℕ} (h : n ≤ m) : (Lower r m ⥤ C) ⥤ (Lower r n ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj (lowerMap r h)

structure FunctorFactorSuccessor {n : ℕ} (a : FunctorFactorAt (C := C) r n) where
  factor : FunctorFactorAt (C := C) r (n + 1)
  restriction : factor.Z ⋙ restrictionBetween r (Nat.le_succ n) ≅ a.Z
  left : Functor.whiskerRight factor.i (restrictionBetween r (Nat.le_succ n)) ≫
    restriction.hom = a.i
  right : restriction.hom ≫ a.p =
    Functor.whiskerRight factor.p (restrictionBetween r (Nat.le_succ n))

namespace FunctorFactorSuccessor
variable {r} (hinj : Function.Injective r.deg)
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {left right : MorphismProperty C} (data : MorphismProperty.FunctorialFactorizationData left right)

abbrev atObject (j : J) (a : FunctorFactorAt (C := C) r (r.deg j)) :
    FunctorFactorSuccessor r a where
  factor :=
    { Z := FunctorDegreeStep.middle r j hinj data a ⋙
        (Functor.whiskeringLeft _ _ C).obj (lowerSuccToUpper r (r.deg j))
      i := Functor.whiskerRight (FunctorDegreeStep.leftTransformation r j hinj data a)
        ((Functor.whiskeringLeft _ _ C).obj (lowerSuccToUpper r (r.deg j)))
      p := Functor.whiskerRight (FunctorDegreeStep.rightTransformation r j hinj data a)
        ((Functor.whiskeringLeft _ _ C).obj (lowerSuccToUpper r (r.deg j)))
      fac := by
        apply NatTrans.ext
        funext φ
        apply NatTrans.ext
        funext x
        exact congr_app (congr_app (FunctorDegreeStep.factor r j hinj data a).fac φ)
          ((lowerSuccToUpper r (r.deg j)).obj x)
      hi := trivial
      hp := trivial }
  restriction := NatIso.ofComponents
    (fun φ ↦ DegreeFactorizationStep.restrictionIso r j hinj φ.hom (a.atArrow φ)
      (data.factorizationData (RelativeExtension.map
        (BoundaryExtension.mapOfNatTrans r j φ.hom) (a.atArrow φ))))
    (fun s ↦ (FactorizationProblem.extensionMap data
      ((a.problemFunctor r j).map s)).degreeRestriction_naturality hinj)
  left := by
    apply NatTrans.ext
    funext φ
    exact DegreeFactorizationStep.leftMap_restriction r j hinj φ.hom (a.atArrow φ)
      (data.factorizationData (RelativeExtension.map
        (BoundaryExtension.mapOfNatTrans r j φ.hom) (a.atArrow φ)))
  right := by
    apply NatTrans.ext
    funext φ
    exact DegreeFactorizationStep.rightMap_restriction r j hinj φ.hom (a.atArrow φ)
      (data.factorizationData (RelativeExtension.map
        (BoundaryExtension.mapOfNatTrans r j φ.hom) (a.atArrow φ)))

lemma atObject_atArrow (j : J) (a : FunctorFactorAt (C := C) r (r.deg j))
    (φ : Arrow (J ⥤ C)) :
    (atObject hinj data j a).factor.atArrow φ =
      (FactorSuccessor.atObject hinj data.factorizationData j (a.atArrow φ)).factor := rfl

variable (r) in
def next (hsurj : Function.Surjective r.deg) (n : ℕ) :
    (a : FunctorFactorAt (C := C) r n) → FunctorFactorSuccessor r a := by
  rcases Classical.indefiniteDescription _ (hsurj n) with ⟨j, hj⟩
  subst n
  intro a
  exact atObject hinj data j a

lemma next_atArrow (hsurj : Function.Surjective r.deg) (n : ℕ)
    (a : FunctorFactorAt (C := C) r n) (φ : Arrow (J ⥤ C)) :
    (next r hinj data hsurj n a).factor.atArrow φ =
      (FactorSuccessor.next r φ.hom hinj data.factorizationData hsurj n (a.atArrow φ)).factor := by
  unfold next FactorSuccessor.next
  generalize Classical.indefiniteDescription (fun k : J ↦ r.deg k = n) (hsurj n) = s
  rcases s with ⟨k, hk⟩
  subst n
  rfl

end FunctorFactorSuccessor
end SerrePositivity.Reedy
