module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveCofibrations
public import SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantObjects
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Postcomposition on actual projective diagram models

Right classes are tested pointwise. An ordinary adjunction lifts to the
diagram categories and gives left Quillen preservation by adjunction.
Evaluation also preserves cofibrations and trivial cofibrations.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.Projective
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

lemma evaluation_isLeftQuillen (k : K) :
    let := modelCategory K I J
    Quillen.IsLeftQuillen (evaluation K (C := C) k) := by
  let := modelCategory K I J
  constructor
  · intro X Y f hf
    exact cofibrations_le_objectwise K I J f hf k
  · intro X Y f hf
    exact ⟨cofibrations_le_objectwise K I J f hf.1 k, hf.2 k⟩

variable {D : Type u'} [Category.{v'} D] [ModelCategory D] [IsLocallyPresentable.{w} D]
  (I' J' : MorphismProperty D) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I' J']

lemma postcompose_isRightQuillen (R : D ⥤ C) [Quillen.IsRightQuillen R] :
    let := modelCategory K I J
    let := modelCategory K I' J'
    Quillen.IsRightQuillen ((Functor.whiskeringRight K D C).obj R) := by
  let := modelCategory K I J
  let := modelCategory K I' J'
  constructor
  · intro X Y p hp k
    exact Quillen.IsRightQuillen.map_fibrations (R := R) (p.app k) (hp k)
  · intro X Y p hp
    have hk (k : K) : trivialFibrations C (R.map (p.app k)) :=
      Quillen.IsRightQuillen.map_trivialFibrations (R := R) (p.app k) ⟨hp.1 k, hp.2 k⟩
    exact ⟨fun k => (hk k).1, fun k => (hk k).2⟩

lemma postcompose_isLeftQuillen {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [Quillen.IsLeftQuillen L] :
    let := modelCategory K I J
    let := modelCategory K I' J'
    Quillen.IsLeftQuillen ((Functor.whiskeringRight K C D).obj L) := by
  have := (Quillen.isLeftQuillen_iff_isRightQuillen adj).mp inferInstance
  have h := postcompose_isRightQuillen K I J I' J' R
  let := modelCategory K I J
  let := modelCategory K I' J'
  have := h
  exact (Quillen.isLeftQuillen_iff_isRightQuillen (adj.whiskerRight K)).mpr inferInstance

lemma postcompose_isCofibrant {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [Quillen.IsLeftQuillen L] (F : K ⥤ C)
    (hF : let := modelCategory K I J; IsCofibrant F) :
    let := modelCategory K I' J'
    IsCofibrant (F ⋙ L) := by
  have h := postcompose_isLeftQuillen K I J I' J' adj
  let := modelCategory K I J
  let := modelCategory K I' J'
  have := h
  have := hF
  have := (adj.whiskerRight K).isLeftAdjoint
  exact Quillen.isCofibrant_obj ((Functor.whiskeringRight K C D).obj L) F

end SerrePositivity.DiagramModel.Projective
