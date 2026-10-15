import SerrePositivity.HomotopicalAlgebra.Foundations
import SerrePositivity.Spectra.General.CircleHomotopySuspension
import SerrePositivity.Spectra.Stable.EnrichedModel
import Lean.Util.CollectAxioms

universe w v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.ModelGeneration SerrePositivity.Quillen
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.SpectrumStabilization
open SerrePositivity.SpectrumLevelModel SerrePositivity.SimplicialModelInputs
open scoped ZeroObject

-- Cone facts need no properness, generation, or specified factorizations.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    [HasZeroObject C] [HasZeroMorphisms C] {X : C} [IsCofibrant X]
    (P : Cylinder X) [P.IsGood] :
    Cofibration (ModelCylinder.coneEndpoint P) ∧
      WeakEquivalence (0 : ModelCylinder.cone P ⟶ (0 : C)) :=
  ⟨ModelCylinder.coneEndpoint_cofibration P, ModelCylinder.coneCollapse_weakEquivalence P⟩

-- Compare to the actual projective homotopy colimit, with four independent
-- object/Hom/generation/localization universe choices.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    [HasZeroObject C] [HasZeroMorphisms C] [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    {H : Type uH} [Category.{vH} H] (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]
    {X S : C} [IsCofibrant X] (P : Cylinder X) [P.IsGood] (q : P.I ⟶ S)
    (sq : IsPushout P.i (0 : X ⨿ X ⟶ (0 : C)) q (0 : (0 : C) ⟶ S)) :
    Nonempty (Q.obj ((HomotopySuspension.functor I J).obj X) ≅ Q.obj S) :=
  ⟨HomotopySuspension.cylinderQuotientIso I J Q P q sq⟩

-- Obtain generation, left properness and the actual action from the
-- constructed localization. None is a new assumption on the localized model.
example [ModelCategory SSet.{u}] [IsLocallyPresentable.{u} PointedSimplicialSet.{u}]
    (K : PointedSimplicialSet.{u})
    [original : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)]
    [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)]
    [CofibrantlyGenerated.{u} (levelGenerators K pointedI.{u}) (levelGenerators K pointedJ.{u})]
    [MorphismProperty.IsStableUnderCobaseChangeAgainst
      (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))]
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
    let G := p.localization.generators
    let hg := p.localization.generated
    let lp := symmetricSpectrum_isLocallyPresentable (K := K)
    let := p.localization.model
    let := hg
    let := lp
    let W := weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)
    Nonempty (W.Q.obj ((HomotopySuspension.functor (levelGenerators K pointedI) G).obj E) ≅
      W.Q.obj (pointwiseTensor PointedSimplicialSet.circle E)) := by
  have : CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} :=
    pointedSimplicial_cofibrantlyGenerated hcof hfib
  have : CofibrantlyGenerated.{u} SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J :=
    simplicial_cofibrantlyGenerated hcof hfib
  have : MonoidalModelCategory PointedSimplicialSet.{u} :=
    pointedSimplicial_monoidalModel hcof hfib
  have : IsCofibrant K := pointedSimplicial_isCofibrant hcof K
  let : EnrichedOrdinaryCategory PointedSimplicialSet.{u}
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) := mappingEnrichedOrdinaryCategory
  have haction := (p.enriched_model K pointedI pointedJ cofSp fibSp hcof hfib
    (fun {A B} _ _ ↦ pointedSimplicial_isCofibrant hcof A)).1
  have hproper := p.leftProper K cofSp fibSp (levelGenerators K pointedI) (levelGenerators K pointedJ)
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J hcof hfib hcof hfib hcof hfib hw
  let G := p.localization.generators
  have hg := p.localization.generated
  have lp := symmetricSpectrum_isLocallyPresentable (K := K)
  let stableModel := p.localization.model
  let := stableModel
  have : CofibrantlyGenerated.{u} (levelGenerators K pointedI) G := hg
  have : IsLocallyPresentable.{u} (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K) := lp
  have : MorphismProperty.IsStableUnderCobaseChangeAgainst
      (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K))
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)) := hproper
  have : IsQuillenBifunctor (pointwiseTensorBifunctor (K := K)) := haction
  have : IsCofibrant E := hE
  exact ⟨circleHomotopySuspensionIso (spectrumModel := stableModel) hcof hw E
    (levelGenerators K pointedI) G (weakEquivalences _).Q⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Pointed.CylinderCone,
    `SerrePositivity.HomotopicalAlgebra.Pointed.HomotopySuspension,
    `SerrePositivity.Spectra.General.CircleHomotopySuspension]
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
  unless modules.size == expected.size do throwError "Some homotopy suspension modules were not audited"
  logInfo m!"Homotopy suspension audit passed: {count} declarations in {modules.size} modules, standard axioms only."
