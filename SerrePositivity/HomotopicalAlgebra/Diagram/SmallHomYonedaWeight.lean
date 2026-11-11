module

public import SerrePositivity.HomotopicalAlgebra.Diagram.YonedaWeightQuillen
public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomConstantWeight

/-! # Yoneda weight comparison in independent source and weight universes -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.DiagramModel.SmallHomYonedaWeight
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
local instance : HasColimitsOfSize.{w, w} (ShrinkHoms C) := by
  have := SmallHomModel.locallyPresentable.{w} C
  exact Smith.locallyPresentable_hasColimits (C := ShrinkHoms C)

variable (A : K ⥤ SimplexCategory ⥤ C)

def iso : YonedaWeightRealization.weightFamily K ⋙ SmallHomFrameWeights.functor K A ≅
    ConstantWeightHom.degree K A (SimplexCategory.mk 0) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (YonedaWeightRealization.iso K (SmallHomFrameWeights.source K A))
      (SmallHomModel.equivalence.{w} C).functor ≪≫
        SmallHomConstantWeight.degreeIso K A (SimplexCategory.mk 0)

variable (IC JC : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IC JC]
  [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

local instance : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable
local instance : IsLocallyPresentable.{w} (Kᵒᵖ ⥤ SSet.{w}) :=
  Smith.AccessibleLimits.functorCategory_isLocallyPresentable Kᵒᵖ

include hcof hfib hA hconst in
lemma map_augmentation_weakEquivalence
    (hzero : let := Projective.modelCategory K IC JC
      IsCofibrant (ConstantWeightHom.degree K A (SimplexCategory.mk 0))) :
    weakEquivalences C ((SmallHomFrameWeights.functor K A).map
      (YonedaHomotopyWeight.augmentation K I J (𝟙_ SSet.{w}))) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := Projective.modelCategory_generated Kᵒᵖ I J
  have := SmallHomFrameWeights.isLeftQuillen K I J hcof hfib A hA hconst
  have := WeightComparison.all_cofibrant hcof (𝟙_ SSet.{w})
  have hvalues := YonedaHomotopyWeight.value_isCofibrant K I J (𝟙_ SSet.{w})
  have hrealized : let := Projective.modelCategory K IC JC
      IsCofibrant (YonedaWeightRealization.weightFamily K ⋙
        SmallHomFrameWeights.functor K A) := by
    let := Projective.modelCategory K IC JC
    have := hzero
    exact isCofibrant_of_cofibration (iso K A).inv
  have hc := QuillenColimitComparison.map_homotopyColimit_comparison_weakEquivalence K
    (Projective.generators Kᵒᵖ I) (Projective.generators Kᵒᵖ J) IC JC
    (SmallHomFrameWeights.adjunction K A)
    (YonedaWeightRealization.weightFamily K) hvalues hrealized
  change weakEquivalences C ((SmallHomFrameWeights.functor K A).map (_ ≫ _))
  rw [Functor.map_comp]
  exact (weakEquivalences C).comp_mem _ _ hc ((weakEquivalences C).of_isIso _)

include hcof hfib hA hconst in
lemma map_weightComparison_weakEquivalence
    (hzero : let := Projective.modelCategory K IC JC
      IsCofibrant (ConstantWeightHom.degree K A (SimplexCategory.mk 0))) :
    weakEquivalences C ((SmallHomFrameWeights.functor K A).map
      (HomotopyCones.weightComparison Kᵒᵖ I J)) := by
  have hLv := map_augmentation_weakEquivalence K A IC JC I J hcof hfib hA hconst hzero
  let := Projective.modelCategory Kᵒᵖ I J
  have := SmallHomFrameWeights.isLeftQuillen K I J hcof hfib A hA hconst
  have := WeightComparison.all_cofibrant hcof (𝟙_ SSet.{w})
  have := YonedaHomotopyWeight.weight_isCofibrant K I J (𝟙_ SSet.{w})
  have := HomotopyCones.weight_isCofibrant Kᵒᵖ I J
  exact Quillen.map_trivialFibration_of_weakAugmentation
    (SmallHomFrameWeights.functor K A)
    (YonedaHomotopyWeight.augmentation K I J (𝟙_ SSet.{w}))
    (HomotopyCones.weightComparison Kᵒᵖ I J)
    (YonedaHomotopyWeight.augmentation_weakEquivalence K I J (𝟙_ SSet.{w}))
    (HomotopyColimit.replacementComparison_trivialFibration Kᵒᵖ I J _) hLv

end SerrePositivity.DiagramModel.SmallHomYonedaWeight
