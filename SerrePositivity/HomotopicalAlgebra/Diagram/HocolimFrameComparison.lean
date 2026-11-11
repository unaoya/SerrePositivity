module

public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceNaturality
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-! # A two-variable natural comparison with the weighted hocolim frame

Both source diagrams and arbitrary targets vary in actual bifunctors.
The remaining weighted-Hom identification and pointwise RMap/holim
comparison are deliberately separate from this common-frame cospan.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.HocolimFrameComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev commonFrame : (K ⥤ C) ⥤ SimplexCategory ⥤ C :=
  FrameOverFunctor.commonObj cof (cosimplicialResolutionFamily cof)
    (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
    (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS)

abbrev hom (A : (K ⥤ C) ⥤ SimplexCategory ⥤ C) : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{v} :=
  FrameOverFunctor.hom A ⋙ (Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib)

abbrev middle : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{v} := hom K fib (commonFrame K I J IS JS cof)
abbrev frameHom : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{v} :=
  hom K fib (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)

abbrev left : (HomotopyColimit.functor K I J).op ⋙ chosenResolutionHom cof fib ⟶
    middle K I J IS JS cof fib :=
  Functor.whiskerRight
    (FrameOverFunctor.homLeft cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS))
    ((Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib))

abbrev right : frameHom K I J IS JS fib ⟶ middle K I J IS JS cof fib :=
  Functor.whiskerRight
    (FrameOverFunctor.homRight cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS))
    ((Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib))

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof hfib hw hcofV in
lemma left_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{v}
    (((left K I J IS JS cof fib).app D).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverFunctor.homLeft_weakEquivalence cof (cosimplicialResolutionFamily cof)
    (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
    (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS) hcofV
    (fun E => WeightedHomotopyColimitFrame.augmentation_weakEquivalence K I J IS JS E hcof hfib hw)
    D ((fibrantTarget fib).obj Y)

include hcof hfib hcofV in
lemma right_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{v}
    (((right K I J IS JS cof fib).app D).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverFunctor.homRight_weakEquivalence cof (cosimplicialResolutionFamily cof)
    (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
    (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS) hcofV
    (fun E => WeightedHomotopyColimitFrame.reedyCofibrant K I J IS JS E hcof hfib)
    D ((fibrantTarget fib).obj Y)

end SerrePositivity.DiagramModel.HocolimFrameComparison
