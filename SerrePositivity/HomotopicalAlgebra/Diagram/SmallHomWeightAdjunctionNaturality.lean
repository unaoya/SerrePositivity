module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomWeightFunctoriality

/-! # Frame naturality of the actual small-Hom weighted adjunctions -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.SmallHomFrameWeights
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{w, w} (ShrinkHoms C) := by
  have := SmallHomModel.locallyPresentable.{w} C
  exact Smith.locallyPresentable_hasColimits (C := ShrinkHoms C)

abbrev homFamily : (K ⥤ SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{w} :=
  (sourceFamily K).op ⋙ FrameWeightRealization.homFamily K ⋙
    (Functor.whiskeringLeft C (ShrinkHoms C) (Kᵒᵖ ⥤ SSet.{w})).obj
      (SmallHomModel.equivalence.{w} C).inverse

omit [ModelCategory C] in
lemma homEquiv_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (W : Kᵒᵖ ⥤ SSet.{w}) (Y : C) (t : (functor K B).obj W ⟶ Y) :
    (adjunction K A).homEquiv W Y ((map K a).app W ≫ t) =
      (adjunction K B).homEquiv W Y t ≫ ((homFamily K).map a.op).app Y := by
  unfold adjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  change (FrameWeightRealization.adjunction K (source K A)).homEquiv W _
    ((SmallHomModel.equivalence.{w} C).toAdjunction.homEquiv _ Y
      ((SmallHomModel.equivalence.{w} C).functor.map
        ((FrameWeightRealization.map K ((sourceFamily K).map a)).app W) ≫ t)) = _
  rw [(SmallHomModel.equivalence.{w} C).toAdjunction.homEquiv_naturality_left]
  exact FrameWeightRealization.homEquiv_frame_naturality K
    ((sourceFamily K).map a) W ((SmallHomModel.equivalence.{w} C).inverse.obj Y) _

abbrev weightedFamily (W : Kᵒᵖ ⥤ SSet.{w}) : (K ⥤ SimplexCategory ⥤ C) ⥤ SSet.{w} ⥤ C :=
  family K ⋙ (Functor.whiskeringLeft SSet.{w} (Kᵒᵖ ⥤ SSet.{w}) C).obj
    (WeightedCones.tensorDiagram Kᵒᵖ W)

abbrev weightedHomFamily (W : Kᵒᵖ ⥤ SSet.{w}) :
    (K ⥤ SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  homFamily K ⋙ (Functor.whiskeringRight C (Kᵒᵖ ⥤ SSet.{w}) SSet.{w}).obj
    (WeightedCones.coneSpace Kᵒᵖ W)

omit [ModelCategory C] in
lemma weightedHomEquiv_frame_naturality {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)
    (W : Kᵒᵖ ⥤ SSet.{w}) (X : SSet.{w}) (Y : C) (t : (weightedFunctor K B W).obj X ⟶ Y) :
    (weightedAdjunction K A W).homEquiv X Y
        (((weightedFamily K W).map a).app X ≫ t) =
      (weightedAdjunction K B W).homEquiv X Y t ≫
        ((weightedHomFamily K W).map a.op).app Y := by
  unfold weightedAdjunction
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  change (WeightedCones.adjunction Kᵒᵖ W).homEquiv X _
    ((adjunction K A).homEquiv ((WeightedCones.tensorDiagram Kᵒᵖ W).obj X) Y
      ((map K a).app ((WeightedCones.tensorDiagram Kᵒᵖ W).obj X) ≫ t)) = _
  rw [homEquiv_frame_naturality K a]
  exact (WeightedCones.adjunction Kᵒᵖ W).homEquiv_naturality_right _ _

end SerrePositivity.DiagramModel.SmallHomFrameWeights
