module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.GlobalFunctorialFactorization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationRestrictionArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.DegreeClassTransfer

/-! # Actual functorial Reedy factorizations with their relative classes

The middle functor and both natural factor transformations are those
constructed from the source factorization functor. Global class membership
is transported from the actual source factor chosen at each degree.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.FunctorFactorizationSequence
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ) {C : Type u'} [Category.{v'} C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C] [HasPushouts C] [HasPullbacks C]
  (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg)
  {left right : MorphismProperty C} (data : MorphismProperty.FunctorialFactorizationData left right)

abbrev previous (φ : Arrow (J ⥤ C)) (j : J) := (stage r hinj hsurj data (r.deg j)).atArrow φ

abbrev boundaryFactor (φ : Arrow (J ⥤ C)) (j : J) := data.factorizationData
  (RelativeExtension.map (BoundaryExtension.mapOfNatTrans r j φ.hom)
    (previous r hinj hsurj data φ j))

def leftStepToGlobalIso (φ : Arrow (J ⥤ C)) (j : J) :
    Arrow.mk (DegreeFactorizationStep.leftMap r j hinj φ.hom
      (previous r hinj hsurj data φ j) (boundaryFactor r hinj hsurj data φ j)) ≅
    Arrow.mk (Functor.whiskerLeft (upperInclusion r (r.deg j))
      (pointTower r hinj hsurj data φ).leftMap) := by
  have h := congrArg (fun a : FactorBelow r φ.hom (r.deg j + 1) ↦
    Arrow.mk (Functor.whiskerLeft (upperToLowerSucc r (r.deg j)) a.i))
      (stage_succ_atObject r hinj hsurj data j φ)
  exact eqToIso h.symm ≪≫ (pointTower r hinj hsurj data φ).leftStageArrowIso (r.deg j)

def rightStepToGlobalIso (φ : Arrow (J ⥤ C)) (j : J) :
    Arrow.mk (DegreeFactorizationStep.rightMap r j hinj φ.hom
      (previous r hinj hsurj data φ j) (boundaryFactor r hinj hsurj data φ j)) ≅
    Arrow.mk (Functor.whiskerLeft (upperInclusion r (r.deg j))
      (pointTower r hinj hsurj data φ).rightMap) := by
  have h := congrArg (fun a : FactorBelow r φ.hom (r.deg j + 1) ↦
    Arrow.mk (Functor.whiskerLeft (upperToLowerSucc r (r.deg j)) a.p))
      (stage_succ_atObject r hinj hsurj data j φ)
  exact eqToIso h.symm ≪≫ (pointTower r hinj hsurj data φ).rightStageArrowIso (r.deg j)

lemma left_mem [left.RespectsIso] (φ : Arrow (J ⥤ C)) :
    reedyLeft r left (pointTower r hinj hsurj data φ).leftMap :=
  reedyLeft_of_degreeIso r hinj φ.hom (previous r hinj hsurj data φ)
    (boundaryFactor r hinj hsurj data φ) _ (leftStepToGlobalIso r hinj hsurj data φ)

lemma right_mem [right.RespectsIso] (φ : Arrow (J ⥤ C)) :
    reedyRight r right (pointTower r hinj hsurj data φ).rightMap :=
  reedyRight_of_degreeIso r hinj φ.hom (previous r hinj hsurj data φ)
    (boundaryFactor r hinj hsurj data φ) _ (rightStepToGlobalIso r hinj hsurj data φ)

variable [left.RespectsIso] [right.RespectsIso]

abbrev functorialFactorizationData : MorphismProperty.FunctorialFactorizationData
    (reedyLeft r left) (reedyRight r right) where
  Z := middleFunctor r hinj hsurj data
  i := leftTransformation r hinj hsurj data
  p := rightTransformation r hinj hsurj data
  fac := (rawFunctorialFactorization r hinj hsurj data).fac
  hi φ := left_mem r hinj hsurj data φ
  hp φ := right_mem r hinj hsurj data φ

include hinj hsurj in
lemma hasFunctorialFactorization [left.HasFunctorialFactorization right] :
    (reedyLeft r left).HasFunctorialFactorization (reedyRight r right) :=
  ⟨⟨functorialFactorizationData r hinj hsurj
    (MorphismProperty.functorialFactorizationData left right)⟩⟩

end SerrePositivity.Reedy.FunctorFactorizationSequence
