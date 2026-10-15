module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalQuillen
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction

/-! # The actual diagonal resolution Hom comparison is a weak equivalence

The proved bisimplicial diagonal theorem applies to the actual rowwise
comparison. This needs neither diagonal cofibrancy of a double source
resolution nor functorial factorizations on the arbitrary model source.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison
variable {C : Type u} [Category.{v} C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma weakEquivalence {A : SimplexCategory ⥤ SimplexCategory ⥤ C} {B : SimplexCategory ⥤ C}
    (a : A ⟶ (Functor.const SimplexCategory).obj B) (Z : C)
    (ha : ∀ n, weakEquivalences SSet.{v} ((DiagonalMappingRows.comparison a Z).app n)) :
    weakEquivalences SSet.{v} ((cosimplicialHomMap (DiagonalFrame.augmentation a)).app Z) := by
  have hD := BisimplicialModel.diagonal_map_weakEquivalence hcof hfib
    (DiagonalMappingRows.comparison a Z) ha
  have h := (weakEquivalences SSet.{v}).comp_mem _ _
    ((weakEquivalences SSet.{v}).of_isIso
      (DiagonalFrame.constantIso ((cosimplicialHom B).obj Z)).inv)
    ((weakEquivalences SSet.{v}).comp_mem _ _ hD
      ((weakEquivalences SSet.{v}).of_isIso (iso A Z).hom))
  change weakEquivalences SSet.{v} (comparison a Z) at h
  exact comparison_eq a Z ▸ h

variable [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C

include hcof hfib in
lemma resolution_weakEquivalence {B : SimplexCategory ⥤ C}
    (q : CofibrantResolution simplex B)
    (hB : reedyLeft simplex (cofibrations C) (initial.to B)) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v}
      ((cosimplicialHomMap (DiagonalFrame.augmentation q.augmentation)).app Z) :=
  weakEquivalence hcof hfib q.augmentation Z
    (DiagonalMappingRows.comparison_weakEquivalence q hcof hB Z)

include hcof hfib in
/-- This is the comparison used by the actual higher-lift action on every model source. -/
lemma liftAction_comparison_weakEquivalence (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (ResolutionLiftAction.comparison X Z) :=
  resolution_weakEquivalence hcof hfib (ResolutionLiftSpace.frame X) X.resolution.cofibrant Z

end SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison
