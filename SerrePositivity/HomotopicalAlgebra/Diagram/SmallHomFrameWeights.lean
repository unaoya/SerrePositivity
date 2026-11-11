module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightQuillen
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomRealization

/-! # Weight realization for arbitrary locally presentable model sources

The original Hom universe v and presentability universe w are independent.
Weights are simplicial sets in w, and the realized objects belong to the
original C. The right adjoint records actual small-Hom frame maps. The
projective Quillen theorem uses only pointwise frame conditions on A.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex SerrePositivity.Quillen

namespace SerrePositivity.DiagramModel.SmallHomFrameWeights
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{w, w} (ShrinkHoms C) := by
  have := SmallHomModel.locallyPresentable.{w} C
  exact Smith.locallyPresentable_hasColimits (C := ShrinkHoms C)

abbrev source (A : K ⥤ SimplexCategory ⥤ C) : K ⥤ SimplexCategory ⥤ ShrinkHoms C :=
  A ⋙ (Functor.whiskeringRight SimplexCategory C (ShrinkHoms C)).obj
    (SmallHomModel.equivalence.{w} C).inverse

abbrev functor (A : K ⥤ SimplexCategory ⥤ C) : (Kᵒᵖ ⥤ SSet.{w}) ⥤ C :=
  FrameWeightRealization.functor K (source K A) ⋙ (SmallHomModel.equivalence.{w} C).functor

abbrev hom (A : K ⥤ SimplexCategory ⥤ C) : C ⥤ Kᵒᵖ ⥤ SSet.{w} :=
  (SmallHomModel.equivalence.{w} C).inverse ⋙ FrameWeightRealization.hom K (source K A)

def adjunction (A : K ⥤ SimplexCategory ⥤ C) : functor K A ⊣ hom K A :=
  (FrameWeightRealization.adjunction K (source K A)).comp
    (SmallHomModel.equivalence.{w} C).toAdjunction

variable [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

local instance : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable

include hcof hfib hA hconst

lemma isLeftQuillen :
    let := Projective.modelCategory Kᵒᵖ I J
    IsLeftQuillen (functor K A) := by
  let := SmallHomModel.modelCategory.{w} C
  let := Projective.modelCategory Kᵒᵖ I J
  have := FrameWeightRealization.isLeftQuillen K I J hcof hfib (source K A)
    (fun k => SmallHomRealization.frame_reedyCofibrant (A.obj k) (hA k))
    (fun k => SmallHomRealization.frame_homotopicallyConstant (A.obj k) (hA k) (hconst k))
  have := SmallHomModel.toOriginal_isLeftQuillen.{w} C
  exact Quillen.isLeftQuillen_comp _ _

lemma isRightQuillen :
    let := Projective.modelCategory Kᵒᵖ I J
    IsRightQuillen (hom K A) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := isLeftQuillen K I J hcof hfib A hA hconst
  exact (isLeftQuillen_iff_isRightQuillen (adjunction K A)).mp inferInstance

omit hcof hfib hA hconst in
abbrev weightedFunctor (W : Kᵒᵖ ⥤ SSet.{w}) : SSet.{w} ⥤ C :=
  WeightedCones.tensorDiagram Kᵒᵖ W ⋙ functor K A

omit hcof hfib hA hconst in
abbrev weightedHom (W : Kᵒᵖ ⥤ SSet.{w}) : C ⥤ SSet.{w} :=
  hom K A ⋙ WeightedCones.coneSpace Kᵒᵖ W

omit hcof hfib hA hconst in
def weightedAdjunction (W : Kᵒᵖ ⥤ SSet.{w}) : weightedFunctor K A W ⊣ weightedHom K A W :=
  (WeightedCones.adjunction Kᵒᵖ W).comp (adjunction K A)

lemma weighted_isLeftQuillen (W : Kᵒᵖ ⥤ SSet.{w})
    (hW : let := Projective.modelCategory Kᵒᵖ I J; IsCofibrant W) :
    IsLeftQuillen (weightedFunctor K A W) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have : IsQuillenBifunctor (CategoryTheory.MonoidalCategory.curriedTensor SSet.{w}) :=
    SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  have := WeightedCones.tensorDiagram_isLeftQuillen Kᵒᵖ I J W hW
  have := isLeftQuillen K I J hcof hfib A hA hconst
  exact Quillen.isLeftQuillen_comp _ _

lemma weighted_isRightQuillen (W : Kᵒᵖ ⥤ SSet.{w})
    (hW : let := Projective.modelCategory Kᵒᵖ I J; IsCofibrant W) :
    IsRightQuillen (weightedHom K A W) := by
  have := weighted_isLeftQuillen K I J hcof hfib A hA hconst W hW
  exact (isLeftQuillen_iff_isRightQuillen (weightedAdjunction K A W)).mp inferInstance

end SerrePositivity.DiagramModel.SmallHomFrameWeights
