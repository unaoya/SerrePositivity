module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationSequence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationRestrictionArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationArrowComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow

/-! # Reedy class membership of the actual globally constructed factors

Global restriction isomorphisms compare each relative arrow with the
selected source factorization at its own degree. The comparisons take
place in arrow categories and therefore transport arbitrary classes which
respect isomorphisms. The conclusion concerns the actual global factors,
not only their finite-stage boundary data.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.FactorizationSequence
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  {F G : J ⥤ C} (τ : F ⟶ G)
  (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)
  {left right : MorphismProperty C}
  (factor : ∀ {A B : C} (f : A ⟶ B), MorphismProperty.MapFactorizationData left right f)

abbrev previous (j : J) := stage r τ hinj hsurj factor (r.deg j)

abbrev boundaryFactor (j : J) := factor
  (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j τ) (previous r τ hinj hsurj factor j))

def leftStepToGlobalIso (j : J) :
    Arrow.mk (DegreeFactorizationStep.leftMap r j hinj τ
      (previous r τ hinj hsurj factor j) (boundaryFactor r τ hinj hsurj factor j)) ≅
    Arrow.mk (Functor.whiskerLeft (upperInclusion r (r.deg j))
      (factorizationData r τ hinj hsurj factor).i) := by
  have h := congrArg (fun a : FactorBelow r τ (r.deg j + 1) ↦
    Arrow.mk (Functor.whiskerLeft (upperToLowerSucc r (r.deg j)) a.i))
      (stage_succ_atObject r τ hinj hsurj factor j)
  exact eqToIso h.symm ≪≫ (factorizationTower r τ hinj hsurj factor).leftStageArrowIso (r.deg j)

def rightStepToGlobalIso (j : J) :
    Arrow.mk (DegreeFactorizationStep.rightMap r j hinj τ
      (previous r τ hinj hsurj factor j) (boundaryFactor r τ hinj hsurj factor j)) ≅
    Arrow.mk (Functor.whiskerLeft (upperInclusion r (r.deg j))
      (factorizationData r τ hinj hsurj factor).p) := by
  have h := congrArg (fun a : FactorBelow r τ (r.deg j + 1) ↦
    Arrow.mk (Functor.whiskerLeft (upperToLowerSucc r (r.deg j)) a.p))
      (stage_succ_atObject r τ hinj hsurj factor j)
  exact eqToIso h.symm ≪≫ (factorizationTower r τ hinj hsurj factor).rightStageArrowIso (r.deg j)

lemma left_mem [left.RespectsIso] :
    reedyLeft r left (factorizationData r τ hinj hsurj factor).i := by
  intro j
  let B := BoundaryDiagram.fromUpperFunctor r j C
  have e := B.mapArrow.mapIso (leftStepToGlobalIso r τ hinj hsurj factor j)
  have h := DegreeFactorizationStep.leftBoundary_mem r j hinj τ
    (previous r τ hinj hsurj factor j) (boundaryFactor r τ hinj hsurj factor j)
  have hg := (left.arrow_iso_iff ((BoundaryDiagram.relativeLatchingArrow r j C).mapIso e)).mp h
  exact hg

lemma right_mem [right.RespectsIso] :
    reedyRight r right (factorizationData r τ hinj hsurj factor).p := by
  intro j
  let B := BoundaryDiagram.fromUpperFunctor r j C
  have e := B.mapArrow.mapIso (rightStepToGlobalIso r τ hinj hsurj factor j)
  have h := DegreeFactorizationStep.rightBoundary_mem r j hinj τ
    (previous r τ hinj hsurj factor j) (boundaryFactor r τ hinj hsurj factor j)
  have hg := (right.arrow_iso_iff ((BoundaryDiagram.relativeMatchingArrow r j C).mapIso e)).mp h
  exact hg

variable [left.RespectsIso] [right.RespectsIso]

abbrev reedyFactorizationData :
    MorphismProperty.MapFactorizationData (reedyLeft r left) (reedyRight r right) τ where
  Z := (factorizationData r τ hinj hsurj factor).Z
  i := (factorizationData r τ hinj hsurj factor).i
  p := (factorizationData r τ hinj hsurj factor).p
  fac := (factorizationData r τ hinj hsurj factor).fac
  hi := left_mem r τ hinj hsurj factor
  hp := right_mem r τ hinj hsurj factor

abbrev reedyOfHasFactorization [left.HasFactorization right] :
    MorphismProperty.MapFactorizationData (reedyLeft r left) (reedyRight r right) τ :=
  reedyFactorizationData r τ hinj hsurj (MorphismProperty.factorizationData left right)

end SerrePositivity.Reedy.FactorizationSequence
