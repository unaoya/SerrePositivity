module

public import SerrePositivity.HomotopicalAlgebra.Diagram.YonedaWeightRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.YonedaHomotopyWeight
public import SerrePositivity.HomotopicalAlgebra.Diagram.QuillenColimitComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightQuillen
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyCones
public import SerrePositivity.HomotopicalAlgebra.Quillen.WeakAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightComparison

/-! # Weak augmentation after frame realization

A projectively cofibrant degree-zero frame diagram suffices for realizing
the universal Yoneda homotopy augmentation to a weak equivalence.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.DiagramModel.YonedaWeightQuillen
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (IC JC : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IC JC]
  [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
local instance : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable
local instance : IsLocallyPresentable.{w} (Kᵒᵖ ⥤ SSet.{w}) :=
  Smith.AccessibleLimits.functorCategory_isLocallyPresentable Kᵒᵖ

include hcof hfib hA hconst in
lemma map_augmentation_weakEquivalence
    (hzero : let := Projective.modelCategory K IC JC
      IsCofibrant (ConstantWeightHom.degree K A (SimplexCategory.mk 0))) :
    weakEquivalences C ((FrameWeightRealization.functor K A).map
      (YonedaHomotopyWeight.augmentation K I J (𝟙_ SSet.{w}))) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := Projective.modelCategory_generated Kᵒᵖ I J
  have := FrameWeightRealization.isLeftQuillen K I J hcof hfib A hA hconst
  have := WeightComparison.all_cofibrant hcof (𝟙_ SSet.{w})
  have hvalues := YonedaHomotopyWeight.value_isCofibrant K I J (𝟙_ SSet.{w})
  have hrealized : let := Projective.modelCategory K IC JC
      IsCofibrant (YonedaWeightRealization.weightFamily K ⋙
        FrameWeightRealization.functor K A) := by
    let := Projective.modelCategory K IC JC
    have := hzero
    exact isCofibrant_of_cofibration (YonedaWeightRealization.iso K A).inv
  have hc := QuillenColimitComparison.map_homotopyColimit_comparison_weakEquivalence K
    (Projective.generators Kᵒᵖ I) (Projective.generators Kᵒᵖ J) IC JC
    (FrameWeightRealization.adjunction K A)
    (YonedaWeightRealization.weightFamily K) hvalues hrealized
  change weakEquivalences C ((FrameWeightRealization.functor K A).map (_ ≫ _))
  rw [Functor.map_comp]
  exact (weakEquivalences C).comp_mem _ _ hc ((weakEquivalences C).of_isIso _)

include hcof hfib hA hconst in
lemma map_weightComparison_weakEquivalence
    (hzero : let := Projective.modelCategory K IC JC
      IsCofibrant (ConstantWeightHom.degree K A (SimplexCategory.mk 0))) :
    weakEquivalences C ((FrameWeightRealization.functor K A).map
      (HomotopyCones.weightComparison Kᵒᵖ I J)) := by
  have hLv := map_augmentation_weakEquivalence K IC JC I J hcof hfib A hA hconst hzero
  let := Projective.modelCategory Kᵒᵖ I J
  have := FrameWeightRealization.isLeftQuillen K I J hcof hfib A hA hconst
  have := WeightComparison.all_cofibrant hcof (𝟙_ SSet.{w})
  have := YonedaHomotopyWeight.weight_isCofibrant K I J (𝟙_ SSet.{w})
  have := HomotopyCones.weight_isCofibrant Kᵒᵖ I J
  exact Quillen.map_trivialFibration_of_weakAugmentation
    (FrameWeightRealization.functor K A)
    (YonedaHomotopyWeight.augmentation K I J (𝟙_ SSet.{w}))
    (HomotopyCones.weightComparison Kᵒᵖ I J)
    (YonedaHomotopyWeight.augmentation_weakEquivalence K I J (𝟙_ SSet.{w}))
    (HomotopyColimit.replacementComparison_trivialFibration Kᵒᵖ I J _) hLv

end SerrePositivity.DiagramModel.YonedaWeightQuillen
