module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationArrowComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow

/-! # Transporting local factor classes to arbitrary global diagram arrows -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (hinj : Function.Injective r.deg)
  {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {F G H : J ⥤ C} (τ : F ⟶ G)
  {left right : MorphismProperty C}
  (a : ∀ j, MorphismProperty.MapFactorizationData ⊤ ⊤
    (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ))
  (q : ∀ j, MorphismProperty.MapFactorizationData left right
    (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) (a j)))

lemma reedyLeft_of_degreeIso [left.RespectsIso] (i : F ⟶ H)
    (e : ∀ j, Arrow.mk (DegreeFactorizationStep.leftMap r j hinj τ (a j) (q j)) ≅
      Arrow.mk (Functor.whiskerLeft (upperInclusion r (r.deg j)) i)) : reedyLeft r left i := by
  intro j
  let B := BoundaryDiagram.fromUpperFunctor r j C
  have ei := B.mapArrow.mapIso (e j)
  have hl := DegreeFactorizationStep.leftBoundary_mem r j hinj τ (a j) (q j)
  exact (left.arrow_iso_iff ((BoundaryDiagram.relativeLatchingArrow r j C).mapIso ei)).mp hl

lemma reedyRight_of_degreeIso [right.RespectsIso] (p : H ⟶ G)
    (e : ∀ j, Arrow.mk (DegreeFactorizationStep.rightMap r j hinj τ (a j) (q j)) ≅
      Arrow.mk (Functor.whiskerLeft (upperInclusion r (r.deg j)) p)) : reedyRight r right p := by
  intro j
  let B := BoundaryDiagram.fromUpperFunctor r j C
  have ei := B.mapArrow.mapIso (e j)
  have hr := DegreeFactorizationStep.rightBoundary_mem r j hinj τ (a j) (q j)
  exact (right.arrow_iso_iff ((BoundaryDiagram.relativeMatchingArrow r j C).mapIso ei)).mp hr

end SerrePositivity.Reedy
