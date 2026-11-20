import SerrePositivity.Spectra.General.SimplicialCylinder
import SerrePositivity.Spectra.General.SimplicialSuspensionComparison
import SerrePositivity.Spectra.Stable.EnrichedModel
import Lean.Util.CollectAxioms

universe u v uC vC
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Quillen SerrePositivity.ModelGeneration
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.SpectrumStabilization
open SerrePositivity.SpectrumLevelModel SerrePositivity.SimplicialModelInputs

-- The underlying quotient theorem is independent of models and spectra.
example {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C]
    [HasBinaryCoproducts C] {X Y : C} (f : X ⟶ Y)
    [HasPushout f (CartesianMonoidalCategory.toUnit X)] :
    IsPushout (PointedObject.adjoinFunctor.map f) (PointedObject.toPoint (PointedObject.adjoin X))
      (PointedObject.cofiberProjection f) (PointedObject.fromPoint (PointedObject.cofiber f)) :=
  PointedObject.cofiber_isPushout f

-- Supply the actual localized action using S2, rather than assuming a
-- simplicial cylinder or Quillen action on the localized model.
example [ModelCategory SSet.{u}] (K : PointedSimplicialSet.{u})
    [original : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
    [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)]
    [CofibrantlyGenerated.{u} (levelGenerators K pointedI.{u}) (levelGenerators K pointedJ.{u})]
    (cofSp : MorphismProperty.FunctorialFactorizationData
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
      (trivialFibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)))
    (fibSp : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
      (fibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)))
    (p : StableModelPresentation.{u} K cofSp fibSp (levelGenerators K pointedI.{u}))
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)
    (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
    (E : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)
    (hE : let := p.localization.model; IsCofibrant E) :
    let := p.localization.model
    ∃ P : Cylinder E, P.IsGood ∧
      ∃ e : P.I ≅
        pointwiseTensor (PointedObject.adjoin (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 1))) E,
      Cofibration (intervalBoundaryTensorMap E) ∧
      IsPushout (intervalBoundaryTensorMap E) (intervalBoundaryCollapse E)
        (circleTensorQuotient E) (circleTensorBasepoint E) ∧
      IsPushout P.i (0 : E ⨿ E ⟶ (mappingTensorFunctor E).obj PointedObject.point)
        (e.hom ≫ circleTensorQuotient E)
        (0 : _ ⟶ pointwiseTensor PointedSimplicialSet.circle E) := by
  have : CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} :=
    pointedSimplicial_cofibrantlyGenerated hcof hfib
  have : MonoidalModelCategory PointedSimplicialSet.{u} :=
    pointedSimplicial_monoidalModel hcof hfib
  have : IsCofibrant K := pointedSimplicial_isCofibrant hcof K
  let : EnrichedOrdinaryCategory PointedSimplicialSet.{u}
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) := mappingEnrichedOrdinaryCategory
  have haction := (p.enriched_model K pointedI pointedJ cofSp fibSp hcof hfib
    (fun {A B} _ _ ↦ pointedSimplicial_isCofibrant hcof A)).1
  let := p.localization.model
  have : IsCofibrant E := hE
  have : IsQuillenBifunctor (pointwiseTensorBifunctor (K := K)) := haction
  refine ⟨simplicialCylinder hcof hw E, simplicialCylinder_isGood hcof hw E, Iso.refl _,
    intervalBoundaryTensorMap_cofibration hcof E, circleTensor_isPushout E,
    ?_⟩
  simpa only [Iso.refl_hom, Category.id_comp] using circleTensor_cylinder_isPushout hcof hw E

-- Compatibility with the old suspension/loop adjunction includes the unit
-- and counit, using the canonical comparison of right adjoints.
example (E : SymmetricSpectrum.{u}) :
    (pointwiseTensorCotensorAdjunction
      (K := PointedSimplicialSet.circle.{u}) PointedSimplicialSet.circle).unit.app E ≫
      simplicialLoopNatIso.hom.app (SymmetricSpectrum.suspensionFunctor.obj E) =
        SymmetricSpectrum.suspensionLoopAdjunction.unit.app E := simplicial_suspensionLoopUnit E

example (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.suspensionFunctor.map (simplicialLoopNatIso.hom.app E) ≫
      SymmetricSpectrum.suspensionLoopAdjunction.counit.app E =
        (pointwiseTensorCotensorAdjunction
          (K := PointedSimplicialSet.circle.{u}) PointedSimplicialSet.circle).counit.app E :=
  simplicial_suspensionLoopCounit E

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.QuillenCylinder,
    `SerrePositivity.Spectra.Pointed.CofiberPushout,
    `SerrePositivity.Spectra.General.Zero,
    `SerrePositivity.Spectra.General.SuspensionPushout,
    `SerrePositivity.Spectra.General.SimplicialCylinder,
    `SerrePositivity.Spectra.General.SimplicialSuspensionComparison]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do throwError "Some suspension geometry modules were not audited"
  logInfo m!"Suspension geometry audit passed: {count} declarations in {modules.size} modules, standard axioms only."
