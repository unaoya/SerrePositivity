module

public import SerrePositivity.Spectra.General.Limits
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleLimits
public import SerrePositivity.HomotopicalAlgebra.Monoidal.ModulePresentability
public import SerrePositivity.Spectra.ModelCategory.LevelAcyclicity
public import SerrePositivity.Spectra.ModelCategory.LevelSmallness

/-! # Local presentability of general symmetric spectra

The underlying category is the actual Mathlib category of modules over Sym(K)
in Day convolution. Functor-category presentability and the proved free-module
criterion give local presentability for every suspension coordinate K.
No model structure or cofibrancy condition on K is needed for this fact.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [IsLocallyPresentable.{w} C]

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C] in
lemma symmetricSequence_isLocallyPresentable :
    IsLocallyPresentable.{w} (SymmetricSequence C) := by
  have : IsLocallyPresentable.{w} (FiniteBijection ⥤ C) :=
    Smith.AccessibleLimits.functorCategory_isLocallyPresentable.{w}
      (C := C) FiniteBijection
  exact this

lemma symmetricSpectrum_isLocallyPresentable (K : C) :
    IsLocallyPresentable.{w} (GeneralSymmetricSpectrum C K) := by
  have := symmetricSequence_isLocallyPresentable (C := C)
  exact MonoidalModulePresentability.isLocallyPresentable
    (SymmetricSequence.tensorPowerSequence K)

/-- Actual level model, with image smallness and presentability derived from C.
No cardinal bounds or SOA hypotheses on spectra are additional inputs. -/
lemma exists_combinatorial_levelModel [ModelCategory C] (K : C)
    (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (heval : ∀ n m : ℕ, J.strictMap
      (GeneralSymmetricSpectrum.freeAt (K := K) n ⋙ GeneralSymmetricSpectrum.evaluation m) ≤
        trivialCofibrations C) :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      m.categoryWithWeakEquivalences.weakEquivalences = levelProperty K (weakEquivalences C) ∧
      m.categoryWithFibrations.fibrations = levelProperty K (fibrations C) ∧
      m.categoryWithCofibrations.cofibrations = (levelGenerators K I).rlp.llp ∧
      (let := m; _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w}
        (levelGenerators K I) (levelGenerators K J)) := by
  have := Smith.locallyPresentable_hasColimits (C := C)
  have := symmetricSpectrum_isLocallyPresentable (K := K)
  have : I.IsSmall.{w} := isSmall_of_smallObjectArgument I
  have : J.IsSmall.{w} := isSmall_of_smallObjectArgument J
  have := levelGenerators_isSmall K I
  have := levelGenerators_isSmall K J
  have := Smith.hasSmallObjectArgument (levelGenerators K I)
  have := Smith.hasSmallObjectArgument (levelGenerators K J)
  let h := levelCells_acyclic_of_evaluated_generators K J heval
  refine ⟨levelModelCategory K I J h, rfl, rfl, rfl, ?_⟩
  exact levelModelCategory_generated K I J h

end SerrePositivity.SpectrumLevelModel
