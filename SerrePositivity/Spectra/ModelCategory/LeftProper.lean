module

public import SerrePositivity.Spectra.ModelCategory.FreeLevelCofibrations
public import SerrePositivity.Spectra.ModelCategory.LevelFromGenerators
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationLeftProper
public import SerrePositivity.Spectra.ModelCategory.Combinatorial

/-! # Left properness of the general level model

The first criterion only requires that evaluated free generators be
cofibrations. A monoidal model with cofibrant unit and coordinate supplies
that test by the explicit free-level induction formula. The conclusion is
about all generated cofibrations, including noncofibrant endpoints.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.ModelGeneration

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory C] (K : C)
  (I : MorphismProperty C) [(levelGenerators K I).HasSmallObjectArgument.{w}]

lemma levelCofibrations_le_levelwise
    (heval : ∀ n m : ℕ, I.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
      cofibrations C) :
    (levelGenerators K I).rlp.llp ≤ levelProperty K (cofibrations C) := by
  intro X Y f hf m
  have : PreservesColimitsOfSize.{w, w} (evaluation (K := K) m) := {}
  apply generatedCofibrations_map_le (evaluation (K := K) m) (levelGenerators K I) ?_ _ hf
  intro A B i hi
  change (⨆ n : ℕ, I.strictMap (freeAt (K := K) n)) i at hi
  rw [MorphismProperty.iSup_iff] at hi
  obtain ⟨n, hi⟩ := hi
  cases hi with
  | map hi => exact heval n m _ (I.map_mem_strictMap _ _ hi)

lemma level_leftProper
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    (heval : ∀ n m : ℕ, I.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
      cofibrations C) :
    (levelProperty K (weakEquivalences C)).IsStableUnderCobaseChangeAgainst
      (levelGenerators K I).rlp.llp :=
  EvaluationFamily.detected_leftProper (fun n : ℕ ↦ evaluation (K := K) n)
    _ (levelCofibrations_le_levelwise K I heval)

lemma level_leftProper_of_cofibrant_coordinate
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)] [IsCofibrant K]
    (hI : I ≤ cofibrations C) :
    (levelProperty K (weakEquivalences C)).IsStableUnderCobaseChangeAgainst
      (levelGenerators K I).rlp.llp := by
  apply level_leftProper K I
  intro n m X Y f hf
  cases hf with
  | map hf =>
    have : Cofibration _ := ⟨hI _ hf⟩
    exact evaluatedFree_cofibration K _ n m

omit [HasColimitsOfSize.{w, w} C]
  [(levelGenerators K I).HasSmallObjectArgument.{w}] in
/-- A left proper, cofibrantly generated actual level model, starting with
local presentability of C and tests on the evaluated free generators. -/
lemma exists_leftProper_combinatorial_levelModel
    [IsLocallyPresentable.{w} C]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    (J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (hevalI : ∀ n m : ℕ, I.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
      cofibrations C)
    (hevalJ : ∀ n m : ℕ, J.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
      trivialCofibrations C) :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      m.categoryWithWeakEquivalences.weakEquivalences = levelProperty K (weakEquivalences C) ∧
      m.categoryWithFibrations.fibrations = levelProperty K (fibrations C) ∧
      m.categoryWithCofibrations.cofibrations = (levelGenerators K I).rlp.llp ∧
      (let := m; _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J)) ∧
      m.categoryWithWeakEquivalences.weakEquivalences.IsStableUnderCobaseChangeAgainst
        m.categoryWithCofibrations.cofibrations := by
  have := Smith.locallyPresentable_hasColimits (C := C)
  have := symmetricSpectrum_isLocallyPresentable (K := K)
  have : I.IsSmall.{w} := isSmall_of_smallObjectArgument I
  have := levelGenerators_isSmall K I
  have := Smith.hasSmallObjectArgument (levelGenerators K I)
  obtain ⟨m, hw, hf, hc, hgen⟩ := exists_combinatorial_levelModel K I J hevalJ
  refine ⟨m, hw, hf, hc, hgen, ?_⟩
  rw [hw, hc]
  exact level_leftProper K I hevalI

omit [HasColimitsOfSize.{w, w} C]
  [(levelGenerators K I).HasSmallObjectArgument.{w}] in
/-- The evaluated-generator conditions are supplied by the actual monoidal
free-level calculation. No cardinal or level SOA is an additional input. -/
lemma exists_leftProper_levelModel_of_monoidal
    [IsLocallyPresentable.{w} C]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)] [IsCofibrant K]
    (J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      m.categoryWithWeakEquivalences.weakEquivalences = levelProperty K (weakEquivalences C) ∧
      m.categoryWithFibrations.fibrations = levelProperty K (fibrations C) ∧
      m.categoryWithCofibrations.cofibrations = (levelGenerators K I).rlp.llp ∧
      (let := m; _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J)) ∧
      m.categoryWithWeakEquivalences.weakEquivalences.IsStableUnderCobaseChangeAgainst
        m.categoryWithCofibrations.cofibrations := by
  apply exists_leftProper_combinatorial_levelModel K I J
  · intro n m X Y f hf
    cases hf with
    | map hf =>
      have hi : I ≤ cofibrations C := by
        rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J]
        exact I.le_llp_rlp
      have : Cofibration _ := ⟨hi _ hf⟩
      exact evaluatedFree_cofibration K _ n m
  · intro n m X Y f hf
    cases hf with
    | map hf =>
      have hj : J ≤ trivialCofibrations C := by
        rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J]
        exact J.le_llp_rlp
      have : Cofibration _ := ⟨(hj _ hf).1⟩
      have : WeakEquivalence _ := ⟨(hj _ hf).2⟩
      exact evaluatedFree_trivialCofibration K _ n m

end SerrePositivity.SpectrumLevelModel
