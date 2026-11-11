module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor

/-! # A cosimplicial frame gives an actual right Quillen Hom functor

The horn lifting theorem supplies fibrations on the fixed horn class;
boundary lifting supplies trivial fibrations for the given simplicial
model. These are transported using explicit equalities of its classes.
-/

@[expose] public section
universe v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))

include hcof hfib hA hconst

lemma cosimplicialHom_isRightQuillen : Quillen.IsRightQuillen (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A) where
  map_fibrations _ _ p hp := by
    have : Fibration p := ⟨hp⟩
    change fibrations SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p)
    rw [hfib]
    exact (SSet.modelCategoryQuillen.fibration_iff _).mp
      (cosimplicialHom_fibration A hA hconst p)
  map_trivialFibrations _ _ p hp := by
    have : Fibration p := ⟨hp.1⟩
    have : WeakEquivalence p := ⟨hp.2⟩
    exact cosimplicialHom_trivialFibration hcof A hA p

lemma cosimplicialHom_hasPointwiseRightDerived {H : Type uH} [Category.{vH} H]
    (L : SSet.{v} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{v})] :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A ⋙ L).HasPointwiseRightDerivedFunctor (weakEquivalences C) := by
  have := cosimplicialHom_isRightQuillen hcof hfib A hA hconst
  infer_instance

end SerrePositivity.HomotopyFunctionComplex
