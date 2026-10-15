module
public import SerrePositivity.HomologicalAlgebra.AlgebraLinearYoneda
public import SerrePositivity.HomologicalAlgebra.KoszulExtComparison
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # The actual coefficient-algebra structure on dual Koszul power systems -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {e : ℕ} (z : Fin e → R)

/-- Dual Koszul complexes with their actual C-module coefficient structure. -/
abbrev algebraKoszulDualFunctor : ModuleCat.{u} C ⥤ CochainComplex (ModuleCat.{u} C) ℕ :=
  algebraLinearYonedaFunctor (toChain (koszulComplex z))

/-- Forgetting C recovers the existing dual Koszul functor on restricted coefficients. -/
def algebraKoszulDualRestrictNatIso :
    algebraKoszulDualFunctor (C := C) z ⋙
        (ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℕ) ≅
      ModuleCat.restrictScalars (algebraMap R C) ⋙ koszulDualModuleFunctor z :=
  algebraLinearYonedaRestrictNatIso (toChain (koszulComplex z))

/-- The actual C-linear power transition is precomposition by the original Koszul chain map. -/
def algebraKoszulDualPowerTransition (n : ℕ) :
    algebraKoszulDualFunctor (C := C) (fun j => z j ^ n) ⟶
      algebraKoszulDualFunctor (C := C) (fun j => z j ^ (n + 1)) :=
  algebraLinearYonedaMap (restrictionMap (DerivedCompletion.powerKoszulTransition R z n) embUp)

/-- The full power system consists of actual C-module complexes and C-linear transitions. -/
def algebraKoszulDualPowerDiagram :
    ℕ ⥤ (ModuleCat.{u} C ⥤ CochainComplex (ModuleCat.{u} C) ℕ) :=
  Functor.ofSequence (algebraKoszulDualPowerTransition (C := C) z)

/-- Restriction preserves the exact existing dual Koszul power transition. -/
lemma algebraKoszulDualRestrictNatIso_power_transition (n : ℕ) :
    Functor.whiskerRight (algebraKoszulDualPowerTransition (C := C) z n)
        ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℕ)) ≫
        (algebraKoszulDualRestrictNatIso (C := C) (fun j => z j ^ (n + 1))).hom =
      (algebraKoszulDualRestrictNatIso (C := C) (fun j => z j ^ n)).hom ≫
        Functor.whiskerLeft (ModuleCat.restrictScalars (algebraMap R C))
          (koszulDualPowerTransition z n) :=
  algebraLinearYonedaRestrictNatIso_chain_map
    (restrictionMap (DerivedCompletion.powerKoszulTransition R z n) embUp)

/-- Actual C-scalars correspond to the existing R-linear coefficient multiplication maps. -/
lemma algebraKoszulDualRestrictNatIso_coefficient_scalar (M : ModuleCat.{u} C) (c : C) :
    ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℕ)).map
        (c • 𝟙 ((algebraKoszulDualFunctor (C := C) z).obj M)) ≫
        (algebraKoszulDualRestrictNatIso (C := C) z).hom.app M =
      (algebraKoszulDualRestrictNatIso (C := C) z).hom.app M ≫
        (koszulDualModuleFunctor z).map
          ((ModuleCat.restrictScalars (algebraMap R C)).map (c • 𝟙 M)) := by
  have h := (algebraKoszulDualRestrictNatIso (C := C) z).hom.naturality (c • 𝟙 M)
  have hm := (algebraKoszulDualFunctor (C := C) z).map_smul c (𝟙 M)
  rw [(algebraKoszulDualFunctor (C := C) z).map_id] at hm
  change ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℕ)).map
      ((algebraKoszulDualFunctor (C := C) z).map (c • 𝟙 M)) ≫
      (algebraKoszulDualRestrictNatIso (C := C) z).hom.app M = _ at h
  rw [hm] at h
  exact h

end SerrePositivity
