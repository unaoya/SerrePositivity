module

public import SerrePositivity.Inputs.Homotopy.KanQuillen
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance

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

namespace SerrePositivity.Inputs.Homotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]

lemma resolutionHom_target_geometricWeakEquivalence (X : C)
    {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) [WeakEquivalence f] :
    SimplicialHomotopy.weakEquivalences
      ((cosimplicialHom (Reedy.cosimplicialResolution X).obj).map f) := by
  let := kanQuillenModel.{v}
  exact cosimplicialHom_geometricWeakEquivalence_of_fibrant
    kanQuillenModel_cofibrations _ (Reedy.cosimplicialResolution X).cofibrant
    kanQuillenModel_weakEquivalences f

lemma resolutionHom_source_geometricWeakEquivalence
    {A B : SimplexCategory ⥤ C} (α : A ⟶ B)
    (hA : Reedy.reedyLeft Reedy.simplex (cofibrations C) (Limits.initial.to A))
    (hB : Reedy.reedyLeft Reedy.simplex (cofibrations C) (Limits.initial.to B))
    (hα : ∀ n, weakEquivalences C (α.app n)) (Y : C) [IsFibrant Y] :
    SimplicialHomotopy.weakEquivalences ((cosimplicialHomMap α).app Y) := by
  let := kanQuillenModel.{v}
  exact cosimplicialHomMap_geometricWeakEquivalence kanQuillenModel_cofibrations
    kanQuillenModel_weakEquivalences α hA hB hα Y

lemma chosenResolutionHom_geometricWeakEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X X' : Cᵒᵖ} (f : X ⟶ X') (hf : weakEquivalences C f.unop)
    {Y Y' : C} (g : Y ⟶ Y') (hg : weakEquivalences C g) :
    SimplicialHomotopy.weakEquivalences
      (((chosenResolutionHom cof fib).map f).app Y ≫
        ((chosenResolutionHom cof fib).obj X').map g) := by
  let := kanQuillenModel.{v}
  exact chosenResolutionHom_map_both_geometricWeakEquivalence kanQuillenModel_cofibrations
    kanQuillenModel_weakEquivalences cof fib f hf g hg

end SerrePositivity.Inputs.Homotopy
