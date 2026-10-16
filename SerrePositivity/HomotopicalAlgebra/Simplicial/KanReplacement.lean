module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom

/-! # A functorial Kan replacement built on the value side

The fixed boundary/horn generators supply functorial factorization in SSet.
No functorial factorization is required of a model category whose mapping
spaces will later be replaced. Product preservation is not asserted.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.ModelGeneration SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.SimplicialModel.KanReplacement
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- The actual value-model factorization, supplied by its proved generators. -/
def factorization : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations SSet.{v}) (fibrations SSet.{v}) := by
  have : CofibrantlyGenerated.{v} SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J :=
    simplicial_cofibrantlyGenerated hcof hfib
  have : (trivialCofibrations SSet.{v}).HasFunctorialFactorization (fibrations SSet.{v}) :=
    hasFunctorialFactorization_trivialCofibration_fibration
      SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J
  exact MorphismProperty.functorialFactorizationData _ _

abbrev functor : SSet.{v} ⥤ SSet.{v} := fibrantTarget (factorization hcof hfib)
abbrev unit : 𝟭 SSet.{v} ⟶ functor hcof hfib := fibrantTargetComparison (factorization hcof hfib)

lemma unit_cofibration (K : SSet.{v}) :
    cofibrations SSet.{v} ((unit hcof hfib).app K) :=
  ((factorization hcof hfib).hi (Arrow.mk (terminal.from K))).1

lemma unit_mono (K : SSet.{v}) : Mono ((unit hcof hfib).app K) := by
  have h := unit_cofibration hcof hfib K
  rw [hcof] at h
  exact h

lemma unit_weakEquivalence (K : SSet.{v}) :
    weakEquivalences SSet.{v} ((unit hcof hfib).app K) :=
  fibrantTargetComparison_weakEquivalence _ K

lemma isFibrant (K : SSet.{v}) : IsFibrant ((functor hcof hfib).obj K) :=
  fibrantTarget_isFibrant _ K

lemma kanComplex (K : SSet.{v}) : SSet.KanComplex ((functor hcof hfib).obj K) := by
  have := isFibrant hcof hfib K
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  rw [← hfib]
  exact mem_fibrations (terminal.from ((functor hcof hfib).obj K))

lemma map_weakEquivalence {K L : SSet.{v}} (f : K ⟶ L) (hf : weakEquivalences SSet.{v} f) :
    weakEquivalences SSet.{v} ((functor hcof hfib).map f) :=
  fibrantTarget_map_weakEquivalence _ f hf

include hfib in
/-- Transport canonical Kan fibrancy to the explicitly supplied value-model fibrations. -/
lemma isFibrant_of_kanComplex (K : SSet.{v}) [SSet.KanComplex K] : IsFibrant K := by
  apply (HomotopicalAlgebra.fibration_iff (terminal.from K)).mpr
  rw [hfib]
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp
    (inferInstanceAs (SSet.KanComplex K))

end SerrePositivity.SimplicialModel.KanReplacement
