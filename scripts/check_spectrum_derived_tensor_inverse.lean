import SerrePositivity.Spectra.Stable.DerivedTensorInverse
import SerrePositivity.Spectra.ModelCategory.LeftProper
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.ModelGeneration SerrePositivity.SpectrumLevelModel
open SerrePositivity.SpectrumStabilization SerrePositivity.Quillen

-- Construct the original model, localization and both ordinary derived functors.
-- The returned equivalence has exactly these tensor functors and inverse.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
    [ModelCategory C] [IsLocallyPresentable.{w} C]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)]
    (K : C) [IsCofibrant K] (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
    (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)
    [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
    (IS JS : MorphismProperty SSet.{w}) [CofibrantlyGenerated.{w} IS JS]
    (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
    (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
    (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences) :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      let := m
      ∃ (cofSp : MorphismProperty.FunctorialFactorizationData
          (cofibrations (GeneralSymmetricSpectrum C K))
          (trivialFibrations (GeneralSymmetricSpectrum C K)))
        (fibSp : MorphismProperty.FunctorialFactorizationData
          (trivialCofibrations (GeneralSymmetricSpectrum C K))
          (fibrations (GeneralSymmetricSpectrum C K)))
        (p : StableModelPresentation.{w} K cofSp fibSp (levelGenerators K I)),
        let := p.localization.model
        let W := weakEquivalences (GeneralSymmetricSpectrum C K)
        ∃ (LK LI LP RP : W.Localization ⥤ W.Localization)
          (α : W.Q ⋙ LK ⟶ tensorLeft ((freeAt (K := K) 0).obj K) ⋙ W.Q)
          (β : W.Q ⋙ LI ⟶ tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ W.Q)
          (γ : W.Q ⋙ LP ⟶ pointwiseTensorFunctor K ⋙ W.Q)
          (ρ : cotensorFunctor K ⋙ W.Q ⟶ W.Q ⋙ RP),
          LK.IsLeftDerivedFunctor α W ∧ LI.IsLeftDerivedFunctor β W ∧
          LP.IsLeftDerivedFunctor γ W ∧ RP.IsRightDerivedFunctor ρ W ∧ LP.IsEquivalence ∧
          ∃ (e d : W.Localization ≌ W.Localization),
            e.functor = LK ∧ e.inverse = LI ∧ d.functor = LP ∧ d.inverse = RP := by
  obtain ⟨m, hW, hF, hC, hgen, hproper⟩ := exists_leftProper_levelModel_of_monoidal K I J
  let := m
  have : CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) := hgen
  have : (weakEquivalences (GeneralSymmetricSpectrum C K)).IsStableUnderCobaseChangeAgainst
      (cofibrations (GeneralSymmetricSpectrum C K)) := hproper
  have := hasFunctorialFactorization_cofibration_trivialFibration
    (levelGenerators K I) (levelGenerators K J)
  have := hasFunctorialFactorization_trivialCofibration_fibration
    (levelGenerators K I) (levelGenerators K J)
  let cofSp := MorphismProperty.functorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K))
  let fibSp := MorphismProperty.functorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K))
  obtain ⟨p⟩ := exists_stableModelPresentation K cofSp fibSp (levelGenerators K I)
    I J (levelGenerators K J) hW hF IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw
  have : ∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n) := fun n ↦
    freeAt_isLeftQuillen_of_level_classes K hW hF n
  have := hasFunctorialFactorization_cofibration_trivialFibration I J
  let cofC := MorphismProperty.functorialFactorizationData
    (cofibrations C) (trivialFibrations C)
  have := general_levelTensor_isQuillen K I J
  have hT0 := p.freeTensor_isLeftQuillen K cofSp fibSp _ hcofV hfibV 0 K
  have hT1 := p.freeTensor_isLeftQuillen K cofSp fibSp _ hcofV hfibV 1 (𝟙_ C)
  have hTP := p.pointwiseTensor_isLeftQuillen K cofSp fibSp _ hcofV hfibV K
  let stableModel : ModelCategory (GeneralSymmetricSpectrum C K) := p.localization.model
  let := stableModel
  let W := weakEquivalences (GeneralSymmetricSpectrum C K)
  have : (tensorLeft ((freeAt (K := K) 0).obj K) ⋙ W.Q).HasPointwiseLeftDerivedFunctor W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ stableModel _ _ stableModel _ _ W.Q
      inferInstance _ hT0
  have : (tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ W.Q).HasPointwiseLeftDerivedFunctor W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ stableModel _ _ stableModel _ _ W.Q
      inferInstance _ hT1
  have : (pointwiseTensorFunctor K ⋙ W.Q).HasPointwiseLeftDerivedFunctor W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ stableModel _ _ stableModel _ _ W.Q
      inferInstance _ hTP
  have : IsLeftQuillen (pointwiseTensorFunctor K) := hTP
  have hR := isRightQuillen_of_isLeftQuillen (pointwiseTensorCotensorAdjunction (K := K) K)
  have : (cotensorFunctor K ⋙ W.Q).HasPointwiseRightDerivedFunctor W :=
    @Quillen.hasPointwiseRightDerivedFunctor _ _ stableModel _ _ stableModel _ _ W.Q
      inferInstance _ hR
  let α := (tensorLeft ((freeAt (K := K) 0).obj K) ⋙ W.Q).totalLeftDerivedCounit W.Q W
  let β := (tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ W.Q).totalLeftDerivedCounit W.Q W
  let γ := (pointwiseTensorFunctor K ⋙ W.Q).totalLeftDerivedCounit W.Q W
  let ρ := (cotensorFunctor K ⋙ W.Q).totalRightDerivedUnit W.Q W
  have hP := p.derived_pointwiseTensor_isEquivalence (levelModel := m)
    K I J cofC cofSp fibSp hcofV hfibV hdom W.Q α β γ
    (hQ := inferInstanceAs (W.Q.IsLocalization W))
    (hα := inferInstanceAs
      (Functor.IsLeftDerivedFunctor
        ((tensorLeft ((freeAt (K := K) 0).obj K) ⋙ W.Q).totalLeftDerived W.Q W) α W))
    (hβ := inferInstanceAs
      (Functor.IsLeftDerivedFunctor
        ((tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ W.Q).totalLeftDerived W.Q W) β W))
    (hγ := inferInstanceAs
      (((pointwiseTensorFunctor K ⋙ W.Q).totalLeftDerived W.Q W).IsLeftDerivedFunctor γ W))
  let d := p.derivedTensorCotensorEquivalence (levelModel := m)
    K I J cofC cofSp fibSp hcofV hfibV hdom W.Q α β γ ρ
    (hQ := inferInstanceAs (W.Q.IsLocalization W))
    (hα := inferInstanceAs (Functor.IsLeftDerivedFunctor
      ((tensorLeft ((freeAt (K := K) 0).obj K) ⋙ W.Q).totalLeftDerived W.Q W) α W))
    (hβ := inferInstanceAs (Functor.IsLeftDerivedFunctor
      ((tensorLeft ((freeAt (K := K) 1).obj (𝟙_ C)) ⋙ W.Q).totalLeftDerived W.Q W) β W))
    (hγ := inferInstanceAs (Functor.IsLeftDerivedFunctor
      ((pointwiseTensorFunctor K ⋙ W.Q).totalLeftDerived W.Q W) γ W))
    (hρ := inferInstanceAs (Functor.IsRightDerivedFunctor
      ((cotensorFunctor K ⋙ W.Q).totalRightDerived W.Q W) ρ W))
  let e := p.canonicalDerivedKTensorEquivalence (levelModel := m)
    K I J cofC cofSp fibSp hcofV hfibV hdom W.Q
    (hQ := inferInstanceAs (W.Q.IsLocalization W))
  exact ⟨m, cofSp, fibSp, p, _, _, _, _, α, β, γ, ρ, inferInstance, inferInstance,
    inferInstance, inferInstance, hP, e, d, rfl, rfl, rfl, rfl⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.DerivedComposition,
    `SerrePositivity.HomotopicalAlgebra.Quillen.DerivedWeakInverse,
    `SerrePositivity.HomotopicalAlgebra.Monoidal.DerivedTensorInverse,
    `SerrePositivity.Spectra.Stable.DerivedTensorInverse]
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
  unless modules.size == expected.size do throwError "Some derived tensor inverse modules were not audited"
  logInfo m!"Derived tensor inverse audit passed: {count} declarations in {modules.size} modules, standard axioms only."
