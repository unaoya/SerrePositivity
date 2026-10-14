module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReduction

/-! # Koszul reduction and the completion unit on the actual derived category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- The scalar cone followed by actual localization inverts all quasi-isomorphisms. -/
lemma scalarConeFunctor_inverts_quasiIso (a : R) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).IsInvertedBy
      (scalarConeFunctor a ⋙ DerivedCategory.Q) := by
  intro K L f hf
  have : QuasiIso f := hf
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr
    (scalarConeFunctor_map_quasiIso R a f)

/-- Two-term Koszul reduction as a functor on arbitrary actual derived objects. -/
def derivedScalarConeFunctor (a : R) : ConcreteDerivedCategory R ⥤ ConcreteDerivedCategory R :=
  Localization.lift (scalarConeFunctor a ⋙ DerivedCategory.Q)
    (scalarConeFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- The derived Koszul functor agrees naturally with the concrete cone of any representative. -/
def derivedScalarConeComparison (a : R) :
    DerivedCategory.Q ⋙ derivedScalarConeFunctor R a ≅ scalarConeFunctor a ⋙ DerivedCategory.Q :=
  Localization.fac (scalarConeFunctor a ⋙ DerivedCategory.Q)
    (scalarConeFunctor_inverts_quasiIso R a) DerivedCategory.Q

/-- Power-Koszul reduction of the standard completion unit, on all actual derived objects. -/
def derivedComplexCompletionReduction (a : R) (n : ℕ) :
    derivedScalarConeFunctor R (a ^ n) ⟶
      derivedComplexCompletionFunctor R a ⋙ derivedScalarConeFunctor R (a ^ n) where
  app X := (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app X)
  naturality {X Y} f := by
    change (derivedScalarConeFunctor R (a ^ n)).map f ≫
        (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app Y) =
      (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app X) ≫
        (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionFunctor R a).map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (derivedScalarConeFunctor R (a ^ n)).map
      ((derivedComplexCompletionUnit R a).naturality f)

/-- The two representative comparisons identify the derived reduction with the concrete unit. -/
lemma derivedComplexCompletionReduction_comparison (a : R) (n : ℕ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedComplexCompletionReduction R a n).app (DerivedCategory.Q.obj K) ≫
        (derivedScalarConeFunctor R (a ^ n)).map
          ((derivedComplexCompletionComparison R a).hom.app K) ≫
        (derivedScalarConeComparison R (a ^ n)).hom.app ((complexCompletionFunctor R a).obj K) =
      (derivedScalarConeComparison R (a ^ n)).hom.app K ≫
        (complexCompletionReductionIso R a K n).hom := by
  change (derivedScalarConeFunctor R (a ^ n)).map ((derivedComplexCompletionUnit R a).app _) ≫
      (derivedScalarConeFunctor R (a ^ n)).map _ ≫ _ = _
  rw [← CategoryTheory.Functor.map_comp_assoc, derivedComplexCompletionUnit_comparison]
  exact (derivedScalarConeComparison R (a ^ n)).hom.naturality (complexCompletionUnit R a K)

/-- The reduction of the standard completion unit is an isomorphism for every representative. -/
lemma derivedComplexCompletionReduction_isIso_Q (a : R) (n : ℕ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((derivedComplexCompletionReduction R a n).app (DerivedCategory.Q.obj K)) := by
  have hc := derivedComplexCompletionReduction_comparison R a n K
  have : IsIso ((derivedComplexCompletionReduction R a n).app (DerivedCategory.Q.obj K) ≫
      ((derivedScalarConeFunctor R (a ^ n)).map
        ((derivedComplexCompletionComparison R a).hom.app K) ≫
      (derivedScalarConeComparison R (a ^ n)).hom.app ((complexCompletionFunctor R a).obj K))) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((derivedScalarConeFunctor R (a ^ n)).map
      ((derivedComplexCompletionComparison R a).hom.app K) ≫
      (derivedScalarConeComparison R (a ^ n)).hom.app ((complexCompletionFunctor R a).obj K))

/-- Every actual derived object has the same power-Koszul quotients as its completion. -/
lemma derivedComplexCompletionReduction_isIso (a : R) (n : ℕ) (X : ConcreteDerivedCategory R) :
    IsIso ((derivedComplexCompletionReduction R a n).app X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have := derivedComplexCompletionReduction_isIso_Q R a n K
  have hn := (derivedComplexCompletionReduction R a n).naturality e.hom
  have : IsIso ((derivedScalarConeFunctor R (a ^ n)).map e.hom ≫
      (derivedComplexCompletionReduction R a n).app X) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((derivedScalarConeFunctor R (a ^ n)).map e.hom) _

/-- The canonical power-Koszul comparison as an isomorphism of actual derived objects. -/
def derivedComplexCompletionReductionIso (a : R) (n : ℕ) (X : ConcreteDerivedCategory R) :
    (derivedScalarConeFunctor R (a ^ n)).obj X ≅
      (derivedScalarConeFunctor R (a ^ n)).obj ((derivedComplexCompletionFunctor R a).obj X) := by
  have := derivedComplexCompletionReduction_isIso R a n X
  exact asIso ((derivedComplexCompletionReduction R a n).app X)

/-- The canonical comparison is natural in all actual derived morphisms. -/
def derivedComplexCompletionReductionNatIso (a : R) (n : ℕ) :
    derivedScalarConeFunctor R (a ^ n) ≅
      derivedComplexCompletionFunctor R a ⋙ derivedScalarConeFunctor R (a ^ n) :=
  NatIso.ofComponents (derivedComplexCompletionReductionIso R a n)
    (fun f => (derivedComplexCompletionReduction R a n).naturality f)

end SerrePositivity.DerivedCompletion
