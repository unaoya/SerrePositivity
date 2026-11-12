module

public import SerrePositivity.HomotopicalAlgebra.Localization.Basic
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameComparison

/-! # The ordinary local test can be computed using any actual source frame

The natural weak cospan of frame comparisons identifies the actual
morphism properties. The frame augmentation need only be degreewise
weak; it is not required to be a Reedy trivial fibration.
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
lemma mappingTest_eq_of_frame (p : CosimplicialFrameFamily (C := C)) (Y : C) :
    mappingTest cof fib Y = MappingTests.test (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom p.obj (fibrantTarget fib))
      (weakEquivalences SSet.{v}) Y := by
  let q := cosimplicialResolutionFamily cof
  let R := fibrantTarget fib
  have hR : ∀ Z, IsFibrant (R.obj Z) := fibrantTarget_isFibrant fib
  have hl := MappingTests.test_eq_of_weakComparison (chosenResolutionHom cof fib)
    (weakEquivalences SSet.{v}) (FrameComparison.homLeft cof q p R)
    (FrameComparison.homLeft_weakEquivalence cof q p hcof R hR) Y
  have hr := MappingTests.test_eq_of_weakComparison (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom p.obj R)
    (weakEquivalences SSet.{v}) (FrameComparison.homRight cof q p R)
    (FrameComparison.homRight_weakEquivalence cof q p hcof R hR) Y
  exact hl.trans hr.symm

end SerrePositivity.Bousfield
