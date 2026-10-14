module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.MonoidAxiom
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Relative cell complexes under colimit-preserving functors

This is the general step needed to verify transfer acyclicity using a monoid
axiom. It does not postulate that forgetting an algebra preserves cell maps.
-/

@[expose] public section
universe w u v u' v'
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Quillen

namespace SerrePositivity.ModelGeneration
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (R : C ⥤ D)

lemma pushouts_inverseImage_le (P : MorphismProperty D) [PreservesColimitsOfShape WalkingSpan R] :
    (P.inverseImage R).pushouts ≤ P.pushouts.inverseImage R := by
  rintro A B f ⟨X, Y, g, a, b, hg, sq⟩
  exact ⟨_, _, R.map g, R.map a, R.map b, hg, sq.map R⟩

lemma colimitsOfShape_inverseImage_le (P : MorphismProperty D)
    (J : Type*) [Category* J] [PreservesColimitsOfShape J R] :
    (P.inverseImage R).colimitsOfShape J ≤ (P.colimitsOfShape J).inverseImage R := by
  intro A B f hf
  cases hf with
  | mk X₁ X₂ c₁ c₂ h₁ h₂ g hg =>
    apply MorphismProperty.colimitsOfShape.mk' (X₁ ⋙ R) (X₂ ⋙ R)
      (R.mapCocone c₁) (R.mapCocone c₂) (isColimitOfPreserves R h₁)
      (isColimitOfPreserves R h₂) (Functor.whiskerRight g R) hg
    intro j
    change R.map (c₁.ι.app j) ≫ R.map (h₁.desc (Cocone.mk c₂.pt (g ≫ c₂.ι))) =
      R.map (g.app j) ≫ R.map (c₂.ι.app j)
    rw [← R.map_comp, ← R.map_comp]
    exact congrArg R.map (h₁.fac (Cocone.mk c₂.pt (g ≫ c₂.ι)) j)

lemma coproducts_inverseImage_le (P : MorphismProperty D)
    [PreservesColimitsOfSize.{w, w} R] :
    MorphismProperty.coproducts.{w} (P.inverseImage R) ≤
      (MorphismProperty.coproducts.{w} P).inverseImage R := by
  intro A B f hf
  rw [MorphismProperty.coproducts_iff] at hf
  obtain ⟨J, hf⟩ := hf
  exact P.colimitsOfShape_le_coproducts J _
    (colimitsOfShape_inverseImage_le R P (Discrete J) _ hf)

lemma transfiniteCompositions_inverseImage_le (P : MorphismProperty D)
    [PreservesColimitsOfSize.{w, w} R] :
    MorphismProperty.transfiniteCompositions.{w} (P.inverseImage R) ≤
      (MorphismProperty.transfiniteCompositions.{w} P).inverseImage R := by
  intro A B f hf
  rw [MorphismProperty.transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  let : PreservesWellOrderContinuousOfShape J R := {}
  exact P.transfiniteCompositionsOfShape_le_transfiniteCompositions J _
    (MorphismProperty.transfiniteCompositionsOfShape_map_of_preserves J R f hf)

/-- All three operations in a relative cell construction commute with R in
this direction, with the relevant preservation assumptions explicit. -/
lemma relativeCells_inverseImage_le (P : MorphismProperty D)
    [PreservesColimitsOfSize.{w, w} R]
    [PreservesColimitsOfShape WalkingSpan R] :
    relativeCells.{w} (P.inverseImage R) ≤ (relativeCells.{w} P).inverseImage R := by
  exact (MorphismProperty.transfiniteCompositions_monotone
    ((MorphismProperty.pushouts_monotone (coproducts_inverseImage_le R P)).trans
      (pushouts_inverseImage_le R _))).trans (transfiniteCompositions_inverseImage_le R _)

lemma relativeCells_map_le (P : MorphismProperty C) (Q : MorphismProperty D)
    (h : P ≤ Q.inverseImage R)
    [PreservesColimitsOfSize.{w, w} R]
    [PreservesColimitsOfShape WalkingSpan R] :
    relativeCells.{w} P ≤ (relativeCells.{w} Q).inverseImage R :=
  (relativeCells_monotone h).trans (relativeCells_inverseImage_le R Q)
end SerrePositivity.ModelGeneration
