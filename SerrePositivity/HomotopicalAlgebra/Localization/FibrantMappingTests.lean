module

public import SerrePositivity.HomotopicalAlgebra.Localization.Basic
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance

/-! # Computing the derived mapping test at an already fibrant target

The specified target replacement can be removed up to weak equivalence
by the proved target invariance. This compares actual simplicial maps,
not just their sets of components.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma mappingTest_iff_at_fibrant {X Z : C} (f : X ⟶ Z) (Y : C) [IsFibrant Y] :
    mappingTest cof fib Y f ↔ weakEquivalences SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((cosimplicialResolutionFamily cof).obj.map f)).app Y) := by
  let a := (cosimplicialResolutionFamily cof).obj.map f
  let q := (fibrantTargetComparison fib).app Y
  have : IsFibrant ((𝟭 C).obj Y) := inferInstanceAs (IsFibrant Y)
  have := fibrantTarget_isFibrant fib Y
  have : WeakEquivalence q := ⟨fibrantTargetComparison_weakEquivalence fib Y⟩
  have hX := cosimplicialHom_weakEquivalence_of_fibrant hcof _
    ((cosimplicialResolutionFamily cof).cofibrant X) q
  have hZ := cosimplicialHom_weakEquivalence_of_fibrant hcof _
    ((cosimplicialResolutionFamily cof).cofibrant Z) q
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).naturality q
  change weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app ((fibrantTarget fib).obj Y)) ↔ _
  constructor
  · intro h
    exact (weakEquivalences SSet.{v}).of_postcomp _ _ hX
      (hn.symm ▸ (weakEquivalences SSet.{v}).comp_mem _ _ hZ h)
  · intro h
    exact (weakEquivalences SSet.{v}).of_precomp _ _ hZ
      (hn ▸ (weakEquivalences SSet.{v}).comp_mem _ _ h hX)

end SerrePositivity.Bousfield
