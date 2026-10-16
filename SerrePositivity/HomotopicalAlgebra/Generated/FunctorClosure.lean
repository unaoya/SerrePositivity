module

public import SerrePositivity.HomotopicalAlgebra.Generated.Basic

/-! # Preservation of generated left classes by colimit preserving functors

The target only carries a morphism property closed under the four cell operations.
No model structure or adjoint on the target is required.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.ModelGeneration
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (W : MorphismProperty D)

lemma inverseImage_colimitsOfShape (J : Type*) [Category* J]
    [PreservesColimitsOfShape J F] [W.IsStableUnderColimitsOfShape J] :
    (W.inverseImage F).IsStableUnderColimitsOfShape J where
  condition X Y c d hc hd α hα f hf := by
    apply MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := W) (X ⋙ F) (Y ⋙ F) (F.mapCocone c) (F.mapCocone d)
      (isColimitOfPreserves F hc) (isColimitOfPreserves F hd)
      (Functor.whiskerRight α F) hα (F.map f)
    intro j
    exact (F.map_comp _ _).symm.trans ((congrArg F.map (hf j)).trans (F.map_comp _ _))

lemma inverseImage_cobaseChange [PreservesColimitsOfShape WalkingSpan F]
    [W.IsStableUnderCobaseChange] : (W.inverseImage F).IsStableUnderCobaseChange where
  of_isPushout sq hf := MorphismProperty.of_isPushout (P := W) (sq.map F) hf

/-- Small colimits and preservation of generating arrows suffice to preserve
the generated left class, with no lifting property imposed on the target. -/
lemma generatedLeft_map (I : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
    [PreservesColimitsOfSize.{w, w} F] [PreservesColimitsOfShape WalkingSpan F]
    [W.IsStableUnderRetracts] [W.IsStableUnderCobaseChange]
    [W.IsStableUnderCoproducts.{w}] [W.IsStableUnderTransfiniteComposition.{w}]
    (hI : I ≤ W.inverseImage F) : I.rlp.llp ≤ W.inverseImage F := by
  let : (W.inverseImage F).IsStableUnderCobaseChange := inverseImage_cobaseChange F W
  let : (W.inverseImage F).IsStableUnderCoproducts.{w} :=
    ⟨fun J => inverseImage_colimitsOfShape F W (Discrete J)⟩
  rw [I.llp_rlp_of_hasSmallObjectArgument']
  refine (MorphismProperty.retracts_le_iff (Q := W.inverseImage F)).mpr ?_
  let J := I.smallObjectκ.ord.ToType
  let : PreservesWellOrderContinuousOfShape J F := ⟨fun _ _ => inferInstance⟩
  intro X Y f hf
  have hc : (MorphismProperty.coproducts.{w} I).pushouts ≤ W.inverseImage F :=
    MorphismProperty.pushouts_le_iff.mpr (MorphismProperty.coproducts_le_iff.mpr hI)
  exact MorphismProperty.transfiniteCompositionsOfShape_le W J _
    (MorphismProperty.transfiniteCompositionsOfShape_map_of_preserves J F f
      (MorphismProperty.transfiniteCompositionsOfShape_monotone J hc _ hf))

end SerrePositivity.ModelGeneration
