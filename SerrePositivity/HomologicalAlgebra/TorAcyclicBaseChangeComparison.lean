module
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeResolution
public import SerrePositivity.HomologicalAlgebra.ScalarExtensionTensorCancellation
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-! # Change the base of Tor for a scalar-extension-acyclic coefficient module -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Tor with a module over S may be computed after base change of an acyclic resolution. -/
def torAcyclicBaseChangeIso (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) (N : ModuleCat.{u} S) (i : ℕ) :
    ((Tor (ModuleCat R) i).obj ((ModuleCat.restrictScalars φ).obj N)).obj M ≅
      (ModuleCat.restrictScalars φ).obj
        (((Tor (ModuleCat S) i).obj N).obj ((ModuleCat.extendScalars φ).obj M)) := by
  let P := projectiveResolution M
  let K := extRes P
  let hK := isResolutionOf_extRes P
  let hKS := isResolutionOf_baseChange_of_torVanishing φ M hK hM
  let L := (((tensoringLeft (ModuleCat S)).obj N).mapHomologicalComplex (.up ℤ)).obj
    (baseChange φ K)
  let e := (Functor.mapHomologicalComplexCompIso (scalarExtensionTensorCancelIso φ N)
    (.up ℤ)).app K
  exact torModuleIsoCochain ((ModuleCat.restrictScalars φ).obj N) hK i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) (-(i : ℤ))).mapIso e.symm ≪≫
    (L.sc (-(i : ℤ))).mapHomologyIso (ModuleCat.restrictScalars φ) ≪≫
    (ModuleCat.restrictScalars φ).mapIso (torModuleIsoCochain N hKS i).symm

/-- If the scalar extension is flat, its vanishing Tor descends to every module over S. -/
lemma tor_isZero_of_acyclicBaseChange_flat (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M)
    (hFlat : Module.Flat S ((ModuleCat.extendScalars φ).obj M))
    (N : ModuleCat.{u} S) (i : ℕ) (hi : 0 < i) :
    IsZero (((Tor (ModuleCat R) i).obj ((ModuleCat.restrictScalars φ).obj N)).obj M) := by
  have := hFlat
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have := torModule_subsingleton_of_flat (R := S) ((ModuleCat.extendScalars φ).obj M) N j
  have := (torModuleComm (R := S) (j + 1) N
    ((ModuleCat.extendScalars φ).obj M)).injective.subsingleton
  have hz : IsZero (((Tor (ModuleCat S) (j + 1)).obj N).obj
      ((ModuleCat.extendScalars φ).obj M)) := ModuleCat.isZero_of_subsingleton _
  exact ((ModuleCat.restrictScalars φ).map_isZero hz).of_iso
    (torAcyclicBaseChangeIso φ M hM N (j + 1))

end SerrePositivity
