module
public import SerrePositivity.HomologicalAlgebra.KoszulExtComparison
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import SerrePositivity.HomologicalAlgebra.SequentialComplexColimits
public import Mathlib.Algebra.Category.ModuleCat.AB

/-! # The actual dual Koszul direct system and its local-cohomology comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- A direct system of actual dual Koszul cochain functors with their actual power transitions. -/
def koszulDualPowerDiagram : ℕ ⥤ (ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ) :=
  Functor.ofSequence (koszulDualPowerTransition z)

/-- The cohomology diagram induced by the actual direct system of dual complexes. -/
def koszulDualPowerHomologyDiagram (i : ℕ) : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  koszulDualPowerDiagram z ⋙
    (Functor.whiskeringRight (ModuleCat R) (CochainComplex (ModuleCat R) ℕ) (ModuleCat R)).obj
      (homologyFunctor (ModuleCat R) (.up ℕ) i)

/-- Convert the double-opposite index of Mathlib's Ext diagram to the usual natural index. -/
def powerKoszulExtDiagram (i : ℕ) : ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙ localCohomology.diagram (powerKoszulIdealDiagram z) i

/-- Compatible augmented comparisons give an isomorphism of entire indexed Ext/Koszul systems. -/
def koszulExtPowerDiagramNatIso (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (i : ℕ) : powerKoszulExtDiagram z i ≅ koszulDualPowerHomologyDiagram z i := by
  let α : powerKoszulExtDiagram z i ⟶ koszulDualPowerHomologyDiagram z i :=
    NatTrans.ofSequence (fun n => (koszulExtComparison _ (hres n) i).hom) (by
      intro n
      simp only [koszulDualPowerHomologyDiagram, koszulDualPowerDiagram,
        Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
        Functor.whiskeringRight_obj_map]
      change (Ext R (ModuleCat R) i).map
          ((localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).map
            (homOfLE (Nat.le_succ n)).op).op ≫ (koszulExtComparison _ (hres (n + 1)) i).hom =
        (koszulExtComparison _ (hres n) i).hom ≫
          Functor.whiskerRight (koszulDualPowerTransition z n)
            (homologyFunctor (ModuleCat R) (.up ℕ) i)
      exact koszulExtComparison_power_transition z n i (hres n) (hres (n + 1)))
  exact NatIso.ofComponents (fun n => koszulExtComparison _ (hres n) i)
    (fun f => α.naturality f)

/-- The colimit of dual Koszul cohomology is naturally Mathlib's local-cohomology functor. -/
def koszulDualPowerHomologyColimitNatIso [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    colimit (koszulDualPowerHomologyDiagram z i) ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  (HasColimit.isoOfNatIso (koszulExtPowerDiagramNatIso z hres i)).symm ≪≫
    Functor.Final.colimitIso (opOp ℕ) (localCohomology.diagram (powerKoszulIdealDiagram z) i) ≪≫
      localCohomologyPowerKoszulIdealNatIso z i

/-- The regular standard parameters supply the resolution conditions at all actual stages. -/
def regularKoszulDualPowerHomologyColimitNatIso [IsLocalRing R] [IsNoetherianRing R]
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z)) (i : ℕ) :
    colimit (koszulDualPowerHomologyDiagram z i) ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  koszulDualPowerHomologyColimitNatIso z (isKoszulResolution_all_powers z hz hreg) i

/-- The actual dual Koszul system as cochain complexes of coefficient functors. -/
def koszulDualFunctorComplexDiagram : ℕ ⥤ CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  koszulDualPowerDiagram z ⋙ functorCochainComplexFunctor (ModuleCat.{u} R) (ModuleCat.{u} R)

/-- The categorical colimit of dual Koszul complexes, with coefficient functoriality. -/
def koszulDualColimitComplex : CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  colimit (koszulDualFunctorComplexDiagram z)

/-- View the dual Koszul colimit as actual cochain complexes depending on the coefficient module. -/
def koszulDualColimitFunctor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  (koszulDualColimitComplex z).asFunctor

/-- Exact sequential colimits identify colimit homology with local cohomology. -/
def koszulDualColimitHomologyNatIso [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    (koszulDualColimitComplex z).homology i ≅ localCohomology (Ideal.span (Set.range z)) i :=
  sequentialCochainHomologyColimitIso (koszulDualFunctorComplexDiagram z) i ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (koszulDualPowerDiagram z)
      (functorCochainHomologyNatIso (ModuleCat.{u} R) (ModuleCat.{u} R) i)) ≪≫
    koszulDualPowerHomologyColimitNatIso z hres i

/-- The actual dual Koszul colimit computes local cohomology naturally. -/
def koszulLocalCohomologyComparison [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  asFunctorCochainHomologyIso (koszulDualColimitComplex z) i ≪≫
    koszulDualColimitHomologyNatIso z hres i

/-- The regular standard parameters give the comparison for every coefficient module. -/
def regularKoszulLocalCohomologyComparison [IsLocalRing R] [IsNoetherianRing R]
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z)) (i : ℕ) :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  koszulLocalCohomologyComparison z (isKoszulResolution_all_powers z hz hreg) i

end SerrePositivity
