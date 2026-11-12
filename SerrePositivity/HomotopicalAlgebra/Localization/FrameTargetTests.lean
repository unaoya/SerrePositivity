module

public import SerrePositivity.HomotopicalAlgebra.Localization.FrameArrowTests
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameRightQuillen

/-! # Removing target replacement from a frame test between fibrant objects

The actual replacement unit induces a weak square by Brown's lemma for the
right Quillen frame-Hom functor. Source resolutions and fibrant replacements
remain the specified data; no new choice of derived mapping space is made.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Bousfield.FrameTargetTests
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma cosimplicialHom_map_iff (A : SimplexCategory ⥤ C)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) :
    weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f) ↔
      weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map ((fibrantTarget fib).map f)) := by
  have := cosimplicialHom_isRightQuillen hcof hfib A hA hconst
  have hw (X : C) [IsFibrant X] : weakEquivalences SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map ((fibrantTargetComparison fib).app X)) := by
    have := fibrantTarget_isFibrant fib X
    have : IsFibrant ((𝟭 C).obj X) := inferInstanceAs (IsFibrant X)
    have : WeakEquivalence ((fibrantTargetComparison fib).app X) :=
      ⟨fibrantTargetComparison_weakEquivalence fib X⟩
    exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_fibrant _ _)
  have hs := congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map ((fibrantTargetComparison fib).naturality f)
  simp only [Functor.map_comp] at hs
  exact FrameArrowTests.weakSquare_iff (weakEquivalences SSet.{v}) _ _ _ _ hs (hw Y) (hw Z)

include hcof hfib in
lemma chosenResolutionHom_map_iff
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (X : C) {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z) :
    weakEquivalences SSet.{v} (((chosenResolutionHom cof fib).obj (Opposite.op X)).map f) ↔
      weakEquivalences SSet.{v}
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((cosimplicialResolutionFamily cof).obj.obj X)).map f) :=
  (cosimplicialHom_map_iff fib hcof hfib _
    ((cosimplicialResolutionFamily cof).cofibrant X)
    ((cosimplicialResolutionFamily cof).atObject X).homotopicallyConstant f).symm

end SerrePositivity.Bousfield.FrameTargetTests
