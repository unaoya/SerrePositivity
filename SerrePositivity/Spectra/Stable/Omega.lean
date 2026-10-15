module

public import SerrePositivity.Spectra.General.Suspension
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown

/-! # Omega spectra for a general suspension coordinate

The predicate is stated directly using the existing bonding maps and the
original weak equivalences of C. Its homotopy invariance is proved for
level-fibrant spectra. It is not defined by a localization test.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C]
  [ModelCategory C] {K : C}

def IsOmegaSpectrum (E : GeneralSymmetricSpectrum C K) : Prop :=
  ∀ n : ℕ, weakEquivalences C (adjointStructureMap E n)

def IsFibrantOmegaSpectrum (E : GeneralSymmetricSpectrum C K) : Prop :=
  (∀ n : ℕ, IsFibrant (level E n)) ∧ IsOmegaSpectrum E

lemma isOmegaSpectrum_iff_of_levelWeakEquivalence
    [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
    {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F)
    (hE : ∀ n : ℕ, IsFibrant (level E n)) (hF : ∀ n : ℕ, IsFibrant (level F n))
    (hf : ∀ n : ℕ, weakEquivalences C (levelMap f n)) :
    IsOmegaSpectrum E ↔ IsOmegaSpectrum F := by
  have := Quillen.tensorLeft_isLeftQuillen K
  have := Quillen.isRightQuillen_of_isLeftQuillen (ihom.adjunction K)
  have hw (n : ℕ) : weakEquivalences C
      ((ihom K).map (levelMap f (n + 1))) := by
    have := hE (n + 1)
    have := hF (n + 1)
    have : WeakEquivalence (levelMap f (n + 1)) := ⟨hf (n + 1)⟩
    exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_fibrant _ _)
  constructor
  · intro h n
    exact (weakEquivalences C).of_precomp _ _ (hf n)
      ((adjointStructureMap_naturality f n).symm ▸
        (weakEquivalences C).comp_mem _ _ (h n) (hw n))
  · intro h n
    exact (weakEquivalences C).of_postcomp _ _ (hw n)
      ((adjointStructureMap_naturality f n) ▸
        (weakEquivalences C).comp_mem _ _ (hf n) (h n))

end SerrePositivity.SpectrumStabilization
