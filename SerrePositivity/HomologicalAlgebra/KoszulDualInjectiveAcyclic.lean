module
public import SerrePositivity.HomologicalAlgebra.InjectiveLinearYoneda
public import SerrePositivity.HomologicalAlgebra.KoszulTransitionDepth
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulComparison

/-! # Acyclicity of the actual dual Koszul colimit on injective coefficients -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open Opposite DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Read the actual inverse Koszul diagram as a direct diagram of dual coefficient functors. -/
def koszulDualInverseDiagram : ℕ ⥤ (ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ) where
  obj n := koszulDualModuleFunctor (fun j => z j ^ n)
  map f := chainLinearYonedaMap
    (restrictionMap ((powerKoszulInverseDiagram z).map f.op) embUp)
  map_id n := by
    change chainLinearYonedaMap
      (restrictionMap ((powerKoszulInverseDiagram z).map (𝟙 (op n))) embUp) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, restrictionMap_id]
    exact chainLinearYonedaMap_id (toChain (powerKoszulTower R z n))
  map_comp f g := by simp [chainLinearYonedaMap_comp]

/-- All maps of the existing direct diagram are duals of the original composed inverse maps. -/
lemma koszulDualPowerDiagram_map_eq_inverse {n m : ℕ} (f : n ⟶ m) :
    (koszulDualPowerDiagram z).map f =
      chainLinearYonedaMap
        (restrictionMap ((powerKoszulInverseDiagram z).map f.op) embUp) := by
  let α : koszulDualPowerDiagram z ⟶ koszulDualInverseDiagram z :=
    NatTrans.ofSequence (fun _ => 𝟙 _) (by
      intro k
      simp [koszulDualPowerDiagram, koszulDualInverseDiagram,
        powerKoszulInverseDiagram, koszulDualPowerTransition])
  simpa [α, koszulDualInverseDiagram] using α.naturality f

/-- With injective coefficients, every positive dual cohomology transition eventually vanishes. -/
lemma koszulDualPowerDiagram_injective_homology_eventually_zero [IsNoetherianRing R]
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n ≤ m,
      homologyMap (((koszulDualPowerDiagram z).map (homOfLE hnm)).app J) i = 0 := by
  obtain ⟨m, hnm, hm⟩ := powerKoszul_negative_homology_proZero z (-(i : ℤ)) (by omega) n
  let f : powerKoszulTower R z m ⟶ powerKoszulTower R z n :=
    (powerKoszulInverseDiagram z).map (homOfLE hnm).op
  have hchain : homologyMap (restrictionMap f embUp) i = 0 := by
    apply (cancel_mono (toChainHomologyIso (powerKoszulTower R z n)
      (koszulComplex_isZero_X_of_pos _) i).hom).mp
    erw [zero_comp, toChainHomologyIso_hom_naturality f
      (koszulComplex_isZero_X_of_pos _) (koszulComplex_isZero_X_of_pos _), hm, comp_zero]
  refine ⟨m, hnm, ?_⟩
  rw [koszulDualPowerDiagram_map_eq_inverse]
  exact chainLinearYonedaMap_homology_eq_zero_of_injective
    (restrictionMap f embUp) J i hchain

/-- An eventually-zero sequential diagram has zero colimit. -/
lemma sequentialModuleColimit_isZero_of_eventually_zero (F : ℕ ⥤ ModuleCat.{u} R)
    (hF : ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m, F.map (homOfLE hnm) = 0) :
    IsZero (colimit F) := by
  have hι : ∀ n : ℕ, colimit.ι F n = 0 := by
    intro n
    obtain ⟨m, hnm, hm⟩ := hF n
    rw [← colimit.w F (homOfLE hnm), hm, zero_comp]
  rw [IsZero.iff_id_eq_zero]
  apply colimit.hom_ext
  intro n
  simp [hι n]

/-- The actual colimit homology comparison before any regular-sequence Ext computation. -/
def koszulDualColimitHomologyDiagramIso (i : ℕ) :
    (koszulDualColimitComplex z).homology i ≅ colimit (koszulDualPowerHomologyDiagram z i) :=
  sequentialCochainHomologyColimitIso (koszulDualFunctorComplexDiagram z) i ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (koszulDualPowerDiagram z)
      (functorCochainHomologyNatIso (ModuleCat.{u} R) (ModuleCat.{u} R) i))

/-- On injective coefficient modules, the actual dual Koszul colimit has no positive cohomology.
No regularity on the finite parameter sequence is required. -/
lemma koszulDualColimit_injective_positive_homology_isZero [IsNoetherianRing R]
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) :
    IsZero (((koszulDualColimitFunctor z).obj J).homology i) := by
  let E := (asFunctorCochainHomologyIso (koszulDualColimitComplex z) i).app J ≪≫
    (koszulDualColimitHomologyDiagramIso z i).app J ≪≫
    colimitObjIsoColimitCompEvaluation (koszulDualPowerHomologyDiagram z i) J
  apply IsZero.of_iso _ E
  apply sequentialModuleColimit_isZero_of_eventually_zero
  intro n
  obtain ⟨m, hnm, hm⟩ := koszulDualPowerDiagram_injective_homology_eventually_zero z J i hi n
  exact ⟨m, hnm, hm⟩

end SerrePositivity
