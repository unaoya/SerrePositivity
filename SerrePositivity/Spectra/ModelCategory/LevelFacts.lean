module

public import SerrePositivity.Spectra.ModelCategory.LevelClasses
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion

/-! # Quillen evaluations and fibrant objects from the actual level classes

These consequences apply to any supplied model with the stated classes,
including the actual existence package, without unfolding its construction.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [ModelCategory C] (K : C)
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  (hW : weakEquivalences (GeneralSymmetricSpectrum C K) = levelProperty K (weakEquivalences C))
  (hF : fibrations (GeneralSymmetricSpectrum C K) = levelProperty K (fibrations C))

include hW hF in
lemma evaluation_isRightQuillen_of_level_classes (n : ℕ) :
    Quillen.IsRightQuillen (evaluation (K := K) n) where
  map_fibrations _ _ _ hf := (hF ▸ hf) n
  map_trivialFibrations _ _ _ hf := ⟨(hF ▸ hf.1) n, (hW ▸ hf.2) n⟩

include hW hF in
lemma freeAt_isLeftQuillen_of_level_classes (n : ℕ) :
    Quillen.IsLeftQuillen (freeAt (K := K) n) := by
  have := evaluation_isRightQuillen_of_level_classes K hW hF n
  exact Quillen.isLeftQuillen_of_isRightQuillen (freeAtAdjunction (K := K) n)

include hF in
lemma isFibrant_iff_levelwise (E : GeneralSymmetricSpectrum C K) :
    IsFibrant E ↔ ∀ n : ℕ, IsFibrant (level E n) := by
  have ht (n : ℕ) : IsTerminal ((evaluation (K := K) n).obj
      (⊤_ (GeneralSymmetricSpectrum C K))) := by
    have := (freeAtAdjunction (K := K) n).isRightAdjoint
    exact terminalIsTerminal.isTerminalObj (evaluation (K := K) n) _
  constructor
  · intro h n
    have hp := (hF ▸ mem_fibrations (terminal.from E)) n
    have : Fibration ((evaluation (K := K) n).map (terminal.from E)) := ⟨hp⟩
    exact (isFibrant_iff_of_isTerminal
      ((evaluation (K := K) n).map (terminal.from E)) (ht n)).mpr inferInstance
  · intro h
    constructor
    rw [hF]
    intro n
    have : Fibration ((evaluation (K := K) n).map (terminal.from E)) :=
      (isFibrant_iff_of_isTerminal
        ((evaluation (K := K) n).map (terminal.from E)) (ht n)).mp (h n)
    exact (fibration_iff ((evaluation (K := K) n).map (terminal.from E))).mp this

end SerrePositivity.SpectrumLevelModel
