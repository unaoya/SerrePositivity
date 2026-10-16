module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionTensorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Closure

/-! # Principal completion commutes with every scalar Koszul cone

Both coordinates may be zero divisors. The comparison extends the original
completion unit; no H⁰ replacement of either derived object is used.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a b : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Completeness for a is stable under the scalar cone for an arbitrary b. -/
lemma derivedScalarCone_isComplete (X : ConcreteDerivedCategory R)
    (hc : IsComplete R a X) :
    IsComplete R a ((derivedScalarConeFunctor R b).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hk := isComplete_of_iso R a e.symm hc
  have hcone := isComplete_Q_mappingCone R a (smulId b K) hk hk
  exact isComplete_of_iso R a
    ((derivedScalarConeComparison R b).symm.app K ≪≫
      (derivedScalarConeFunctor R b).mapIso e) hcone

/-- The b-cone of the actual a-completion unit is an a-completion equivalence. -/
lemma scalarCone_completionUnit_map_isIso (X : D) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((derivedScalarConeFunctor R b).map ((derivedComplexCompletionUnit R a).app X.obj))) := by
  let F := derivedComplexCompletionFunctor R a
  let f := (boundedAboveDerivedCompletionUnit R a).app X
  have hf := completionEquivalence_whiskerLeft R a f
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) (boundedAboveKoszulObject b)
  have hn := boundedAboveDerivedTensorKoszulIso_naturality b f
  let eX := boundedAboveDerivedTensorKoszulIso b X
  let eY := boundedAboveDerivedTensorKoszulIso b
    ((boundedAboveDerivedCompletionFunctor R a).obj X)
  change (boundedAboveKoszulObject b ◁ f).hom ≫ eY.hom =
    eX.hom ≫ (derivedScalarConeFunctor R b).map f.hom at hn
  have he : IsIso (F.map eX.hom ≫ F.map ((derivedScalarConeFunctor R b).map f.hom)) := by
    rw [← F.map_comp]
    rw [← hn, F.map_comp]
    exact inferInstance
  dsimp only [f, boundedAboveDerivedCompletionUnit, ObjectProperty.homMk] at he
  exact IsIso.of_isIso_comp_left (F.map eX.hom) _

/-- Extend the original scalar-cone unit to the complete scalar-cone target. -/
def completionScalarConeComparison (X : D) :
    (derivedComplexCompletionFunctor R a).obj ((derivedScalarConeFunctor R b).obj X.obj) ⟶
      (derivedScalarConeFunctor R b).obj ((derivedComplexCompletionFunctor R a).obj X.obj) :=
  (derivedComplexCompletionFunctor R a).map
      ((derivedScalarConeFunctor R b).map ((derivedComplexCompletionUnit R a).app X.obj)) ≫
    (derivedComplexCompletionUnitIso R a _
      (derivedScalarCone_isComplete R a b _
        (derivedComplexCompletionFunctor_isComplete R a X.obj))).inv

/-- This extension has exactly the original scalar-cone completion-unit diagram. -/
lemma completionScalarConeComparison_unit (X : D) :
    (derivedComplexCompletionUnit R a).app ((derivedScalarConeFunctor R b).obj X.obj) ≫
        completionScalarConeComparison R a b X =
      (derivedScalarConeFunctor R b).map ((derivedComplexCompletionUnit R a).app X.obj) :=
  (derivedComplexCompletionHomEquiv R a _ _
    (derivedScalarCone_isComplete R a b _
      (derivedComplexCompletionFunctor_isComplete R a X.obj))).apply_symm_apply _

/-- Actual a-completion and the b-cone commute by the original unit-normalized map. -/
lemma completionScalarConeComparison_isIso (X : D) :
    IsIso (completionScalarConeComparison R a b X) := by
  dsimp only [completionScalarConeComparison]
  have := scalarCone_completionUnit_map_isIso R a b X
  infer_instance

/-- The standard comparison is an isomorphism of the original derived objects. -/
def completionScalarConeIso (X : D) :
    (derivedComplexCompletionFunctor R a).obj ((derivedScalarConeFunctor R b).obj X.obj) ≅
      (derivedScalarConeFunctor R b).obj ((derivedComplexCompletionFunctor R a).obj X.obj) := by
  have := completionScalarConeComparison_isIso R a b X
  exact asIso (completionScalarConeComparison R a b X)

/-- Reflection uniqueness preserves every original bounded-above derived morphism. -/
lemma completionScalarConeComparison_naturality {X Y : D} (f : X ⟶ Y) :
    (derivedComplexCompletionFunctor R a).map ((derivedScalarConeFunctor R b).map f.hom) ≫
        completionScalarConeComparison R a b Y =
      completionScalarConeComparison R a b X ≫
        (derivedScalarConeFunctor R b).map ((derivedComplexCompletionFunctor R a).map f.hom) := by
  apply derivedComplexCompletionHom_ext R a
    (derivedScalarCone_isComplete R a b _ (derivedComplexCompletionFunctor_isComplete R a Y.obj))
  have hr := (derivedComplexCompletionUnit R a).naturality
    ((derivedScalarConeFunctor R b).map f.hom)
  simp only [Functor.id_map] at hr
  rw [← Category.assoc, ← hr, Category.assoc, completionScalarConeComparison_unit,
    ← Category.assoc, completionScalarConeComparison_unit,
    ← Functor.map_comp, ← Functor.map_comp]
  simpa only [Functor.id_map] using congrArg (derivedScalarConeFunctor R b).map
    ((derivedComplexCompletionUnit R a).naturality f.hom)

/-- The unit-normalized comparisons assemble into a natural isomorphism. -/
def completionScalarConeNatIso :
    DerivedCategory.Minus.ι ⋙ derivedScalarConeFunctor R b ⋙ derivedComplexCompletionFunctor R a ≅
      DerivedCategory.Minus.ι ⋙ derivedComplexCompletionFunctor R a ⋙ derivedScalarConeFunctor R b :=
  NatIso.ofComponents (completionScalarConeIso R a b)
    (fun f => completionScalarConeComparison_naturality R a b f)

end SerrePositivity.DerivedCompletion
