module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleRelativeBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialFactorizationClasses
public import Mathlib.Logic.Equiv.Option

/-! # Accessibility of the constructed functorial Reedy factorization

The induction concerns the actual finite-stage functors. At the newly
adjoined object the functor is the source factorization applied to the
relative boundary arrow; at every old object it is the previous stage.
-/

@[expose] public section
universe w v u v' u' s t
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy

private lemma accessiblePrecomposition {B : Type t} [Category.{s} B]
    {E : Type u} [Category.{v} E] {C : Type u'} [Category.{v'} C]
    [HasColimitsOfSize.{w, w} C] (f : B ⥤ E) :
    ((Functor.whiskeringLeft B E C).obj f).IsAccessible.{w} := by
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  exact Functor.isAccessible_of_isCardinalAccessible _ (Cardinal.aleph0 : Cardinal.{w})

private lemma accessibleEvaluation {B : Type t} [Category.{s} B]
    {C : Type u'} [Category.{v'} C] [HasColimitsOfSize.{w, w} C] (b : B) :
    ((evaluation B C).obj b).IsAccessible.{w} := by
  have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
  have : ((evaluation B C).obj b).IsCardinalAccessible (Cardinal.aleph0 : Cardinal.{w}) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact Functor.isAccessible_of_isCardinalAccessible _ (Cardinal.aleph0 : Cardinal.{w})

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [IsLocallyPresentable.{w} C] [HasPushouts C] [HasPullbacks C] [Small.{w} J]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C]
  [∀ j, EssentiallySmall.{w} (MatchingIndex r j)]
  (hinj : Function.Injective r.deg)
  {left right : MorphismProperty C} (data : MorphismProperty.FunctorialFactorizationData left right)
  [data.Z.IsAccessible.{w}]

namespace FunctorDegreeStep

abbrev middleAdjoin (j : J) (a : FunctorFactorAt (C := C) r (r.deg j)) :=
  a.problemFunctor r j ⋙ FactorizationProblem.extensionFunctor r j C data ⋙
    BoundaryDiagram.toAdjoinFunctor r j C

lemma middle_isAccessible (j : J) (a : FunctorFactorAt (C := C) r (r.deg j))
    [a.Z.IsAccessible.{w}] : (middle r j hinj data a).IsAccessible.{w} := by
  have : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
  have hrel := FunctorFactorAt.relativeArrow_isAccessible.{w} r j a
  have : Small.{w} (Lower r (r.deg j)) := small_of_injective
    (f := fun x : Lower r (r.deg j) ↦ x.obj)
    (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)
  have : Small.{w} (Adjoin r j) := small_of_injective
    (Equiv.optionCongr (equivShrink (Lower r (r.deg j)))).injective
  have : ∀ x, (middleAdjoin r data j a ⋙ (evaluation (Adjoin r j) C).obj x).IsAccessible.{w} := by
    rintro (_ | x)
    · exact inferInstanceAs ((FunctorFactorAt.relativeArrow r j a ⋙ data.Z).IsAccessible.{w})
    · have := accessibleEvaluation.{w} (C := C) x
      exact inferInstanceAs ((a.Z ⋙ (evaluation _ C).obj x).IsAccessible.{w})
  have := Smith.functorCategory_isAccessible.{w} (middleAdjoin r data j a)
  have := accessiblePrecomposition.{w} (C := C) (degreeIndex r j hinj)
  exact inferInstanceAs ((middleAdjoin r data j a ⋙
    (Functor.whiskeringLeft _ _ C).obj (degreeIndex r j hinj)).IsAccessible.{w})

end FunctorDegreeStep

namespace FunctorFactorSuccessor

lemma atObject_isAccessible (j : J) (a : FunctorFactorAt (C := C) r (r.deg j))
    [a.Z.IsAccessible.{w}] : ((atObject hinj data j a).factor.Z).IsAccessible.{w} := by
  have : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
  have := FunctorDegreeStep.middle_isAccessible.{w} r hinj data j a
  have := accessiblePrecomposition.{w} (C := C) (lowerSuccToUpper r (r.deg j))
  exact inferInstanceAs ((FunctorDegreeStep.middle r j hinj data a ⋙
    (Functor.whiskeringLeft _ _ C).obj (lowerSuccToUpper r (r.deg j))).IsAccessible.{w})

lemma next_isAccessible (hsurj : Function.Surjective r.deg) (n : ℕ)
    (a : FunctorFactorAt (C := C) r n) [a.Z.IsAccessible.{w}] :
    ((next r hinj data hsurj n a).factor.Z).IsAccessible.{w} := by
  unfold next
  generalize Classical.indefiniteDescription (fun k : J ↦ r.deg k = n) (hsurj n) = s
  rcases s with ⟨j, hj⟩
  subst n
  exact atObject_isAccessible r hinj data j a

end FunctorFactorSuccessor

namespace FunctorFactorizationSequence
variable (hsurj : Function.Surjective r.deg)

lemma stage_isAccessible (n : ℕ) : ((stage r hinj hsurj data n).Z).IsAccessible.{w} := by
  have : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
  induction n with
  | zero =>
    have : Fact Cardinal.aleph0.IsRegular := Cardinal.fact_isRegular_aleph0
    have := Smith.AccessibleFactorization.arrow_left_isCardinalAccessible
      (C := J ⥤ C) (Cardinal.aleph0 : Cardinal.{w})
    have := Functor.isAccessible_of_isCardinalAccessible
      (Arrow.leftFunc : Arrow (J ⥤ C) ⥤ (J ⥤ C)) (Cardinal.aleph0 : Cardinal.{w})
    have := accessiblePrecomposition.{w} (C := C) (lowerInclusion r 0)
    exact inferInstanceAs ((Arrow.leftFunc ⋙ restrictionFunctor (C := C) r 0).IsAccessible.{w})
  | succ n ih =>
    have := ih
    exact FunctorFactorSuccessor.next_isAccessible r hinj data hsurj n (stage r hinj hsurj data n)

lemma middleFunctor_isAccessible : (middleFunctor r hinj hsurj data).IsAccessible.{w} := by
  have : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
  have : ∀ j, (middleFunctor r hinj hsurj data ⋙ (evaluation J C).obj j).IsAccessible.{w} := by
    intro j
    have := stage_isAccessible r hinj data hsurj (r.deg j + 1)
    have := accessibleEvaluation.{w} (C := C) (⟨j, Nat.lt_succ_self _⟩ : Lower r (r.deg j + 1))
    exact inferInstanceAs (((stage r hinj hsurj data (r.deg j + 1)).Z ⋙
      (evaluation _ C).obj ⟨j, Nat.lt_succ_self _⟩).IsAccessible.{w})
  exact Smith.functorCategory_isAccessible.{w} _

end FunctorFactorizationSequence
end SerrePositivity.Reedy
