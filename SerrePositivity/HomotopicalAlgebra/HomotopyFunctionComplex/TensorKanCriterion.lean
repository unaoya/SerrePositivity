module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SubcomplexTensor
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Kan fibrations from actual horn tensor maps

This reduces the Kan assertion for a cosimplicial Hom to source trivial
cofibrations of the constructed finite horn tensor maps. `HornTensor`
establishes that condition for every constructed cofibrant resolution.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] (A : SimplexCategory ⥤ C)

lemma fibration_of_hornTensors
    (hA : ∀ (n : ℕ) (i : Fin (n + 2)), trivialCofibrations C
      (SubcomplexTensor.inclusion (SSet.horn.{v} (n + 1) i) A))
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] : Fibration ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro K L f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  have : HasLiftingProperty (SubcomplexTensor.inclusion (SSet.horn.{v} (n + 1) i) A) p :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (hA n i) (mem_fibrations p)
  exact SubcomplexTensor.hasLiftingProperty _ A p

lemma kanComplex_of_hornTensors
    (hA : ∀ (n : ℕ) (i : Fin (n + 2)), trivialCofibrations C
      (SubcomplexTensor.inclusion (SSet.horn.{v} (n + 1) i) A))
    (Y : C) [IsFibrant Y] : SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) := by
  have : Fibration ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map (terminal.from Y)) :=
    fibration_of_hornTensors A hA (terminal.from Y)
  exact (isFibrant_iff_of_isTerminal ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map (terminal.from Y))
    (terminalIsTerminal.isTerminalObj (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A) (⊤_ C))).mpr this

lemma boundary_lifting_of_cofibration
    (hA : ∀ (n : ℕ), cofibrations C (SubcomplexTensor.inclusion (SSet.boundary.{v} n) A))
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{v} n).ι ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) := by
  have : HasLiftingProperty (SubcomplexTensor.inclusion (SSet.boundary.{v} n) A) p :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ (hA n) (mem_trivialFibrations p)
  exact SubcomplexTensor.hasLiftingProperty _ A p

end SerrePositivity.HomotopyFunctionComplex
