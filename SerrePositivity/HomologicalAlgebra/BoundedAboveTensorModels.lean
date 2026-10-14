module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveProjectiveResolution
public import SerrePositivity.PerfectComplex.TensorBoundedAbove

/-! # Resolution models of the bounded-above derived tensor product

The comparison keeps the augmentation to the ordinary tensor complex.
Functorial localization and derived base change are subsequent constructions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
namespace BoundedAboveProjectiveResolution

/-- Total tensor complex of two projective replacements. -/
abbrev tensorModel (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) := cochainTensor P.complex Q.complex

/-- Standard augmentation to the ordinary tensor complex. -/
def tensorAugmentation (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) : tensorModel P Q ⟶ cochainTensor K L :=
  cochainTensorMap P.π Q.π

/-- Simultaneous changes of both replacements are homotopy equivalences. -/
def tensorComparisonEquiv (P P' : BoundedAboveProjectiveResolution K)
    (Q Q' : BoundedAboveProjectiveResolution L) :
    HomotopyEquiv (tensorModel P Q) (tensorModel P' Q') :=
  cochainTensorHomotopyEquiv (comparisonHomotopyEquiv P P') (comparisonHomotopyEquiv Q Q')

lemma tensorComparisonEquiv_hom (P P' : BoundedAboveProjectiveResolution K)
    (Q Q' : BoundedAboveProjectiveResolution L) :
    (tensorComparisonEquiv P P' Q Q').hom =
      cochainTensorMap (comparison P P') (comparison Q Q') := by
  simp [tensorComparisonEquiv, cochainTensorHomotopyEquiv, comparisonHomotopyEquiv_hom]

/-- The equivalence preserves the standard augmentation up to homotopy. -/
def tensorComparisonAugmentationHomotopy (P P' : BoundedAboveProjectiveResolution K)
    (Q Q' : BoundedAboveProjectiveResolution L) :
    Homotopy ((tensorComparisonEquiv P P' Q Q').hom ≫ tensorAugmentation P' Q')
      (tensorAugmentation P Q) := by
  rw [tensorComparisonEquiv_hom, tensorAugmentation, cochainTensorMap_comp]
  exact (cochainTensorHomotopyLeft (comparisonHomotopy P P') _).trans
    (cochainTensorHomotopyRight _ (comparisonHomotopy Q Q'))

/-- An actual object of the standard derived category. -/
def derivedTensorModel (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) : DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (tensorModel P Q)

/-- The model is independent of the replacements in the actual derived category. -/
def derivedTensorComparisonIso (P P' : BoundedAboveProjectiveResolution K)
    (Q Q' : BoundedAboveProjectiveResolution L) :
    derivedTensorModel P Q ≅ derivedTensorModel P' Q' :=
  asIso (DerivedCategory.Q.map (tensorComparisonEquiv P P' Q Q').hom)

lemma derivedTensorComparisonIso_augmentation (P P' : BoundedAboveProjectiveResolution K)
    (Q Q' : BoundedAboveProjectiveResolution L) :
    (derivedTensorComparisonIso P P' Q Q').hom ≫
        DerivedCategory.Q.map (tensorAugmentation P' Q') =
      DerivedCategory.Q.map (tensorAugmentation P Q) := by
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = _
  rw [← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
    (tensorComparisonAugmentationHomotopy P P' Q Q')

end BoundedAboveProjectiveResolution
end SerrePositivity
