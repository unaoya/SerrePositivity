module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.KanQuillen
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenComparison

/-! # Resolution Hom over the fixed Kan–Quillen value model

This upper entry supplies only the existing HT-KQ value-model input. The
source category is an arbitrary model category. The shared construction
and invariance proofs remain independent of this literature input.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs
variable {C : Type u} [Category.{v} C] [ModelCategory C]

lemma resolutionHom_target_geometricWeakEquivalence (X : C)
    {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    SimplicialHomotopy.weakEquivalences
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (Reedy.cosimplicialResolution X).obj).map f) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel.{v}
  exact cosimplicialHom_geometricWeakEquivalence_of_fibrant
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _ (Reedy.cosimplicialResolution X).cofibrant
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_weakEquivalences f

lemma resolutionHom_source_geometricWeakEquivalence
    {A B : SimplexCategory ⥤ C} (α : A ⟶ B)
    (hA : Reedy.reedyLeft Reedy.simplex (cofibrations C) (Limits.initial.to A))
    (hB : Reedy.reedyLeft Reedy.simplex (cofibrations C) (Limits.initial.to B))
    (hα : ∀ n, weakEquivalences C (α.app n)) (Y : C) [IsFibrant Y] :
    SimplicialHomotopy.weakEquivalences ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel.{v}
  exact cosimplicialHomMap_geometricWeakEquivalence _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_weakEquivalences α hA hB hα Y

lemma chosenResolutionHom_geometricWeakEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') (hf : weakEquivalences C f.unop)
    {Y Y' : C} (g : Y ⟶ Y') (hg : weakEquivalences C g) :
    SimplicialHomotopy.weakEquivalences
      (((chosenResolutionHom cof fib).map f).app Y ≫
        ((chosenResolutionHom cof fib).obj X').map g) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel.{v}
  exact chosenResolutionHom_map_both_geometricWeakEquivalence _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_weakEquivalences cof fib f hf g hg

lemma chosenResolutionHom_choices_geometricWeakEquivalences
    (cof₁ cof₂ : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C))
    (fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C))
    (X : Cᵒᵖ) (Y : C) :
    SimplicialHomotopy.weakEquivalences
        (((ChosenComparison.left cof₁ cof₁ cof₂ fib₁ fib₁ fib₂).app X).app Y) ∧
      SimplicialHomotopy.weakEquivalences
        (((ChosenComparison.right cof₁ cof₁ cof₂ fib₁ fib₁ fib₂).app X).app Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel.{v}
  exact ChosenComparison.geometricWeakEquivalences cof₁ cof₁ cof₂ fib₁ fib₁ fib₂
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_weakEquivalences X Y

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs
