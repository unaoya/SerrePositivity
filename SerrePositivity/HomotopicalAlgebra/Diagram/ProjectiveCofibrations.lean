module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap

/-! # Projective cofibrations are objectwise cofibrations

Evaluation of a free generator is an actual coproduct of that generator.
Evaluation preserves the relative cell construction and retracts, so it
sends every projective cofibration to a cofibration. The converse is not
asserted, and no injective diagram model is used.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.Projective
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w,w} C := Smith.locallyPresentable_hasColimits (C := C)

lemma free_map_cofibration (k l : K) {X Y : C} (f : X ⟶ Y) [Cofibration f] :
    cofibrations C (((free K k).map f).app l) :=
  mem_cofibrations (Limits.Sigma.map (fun _ : k ⟶ l ↦ f))

include J in
lemma freeGenerators_cofibrations (l : K) :
    generators K I ≤ (cofibrations C).inverseImage (evaluation K l) := by
  intro A B f hf
  change (⨆ k, I.strictMap (free K k)) f at hf
  rw [MorphismProperty.iSup_iff] at hf
  obtain ⟨k, hf⟩ := hf
  cases hf with
  | @map X Y f hf =>
    have h : cofibrations C f :=
      (I.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J).symm.le) _ hf
    have : Cofibration f := ⟨h⟩
    exact free_map_cofibration K k l f

omit [IsLocallyPresentable.{w} C] in
lemma cofibration_cells : Quillen.relativeCells.{w} (cofibrations C) ≤ cofibrations C := by
  rw [← trivialFibrations_llp]
  exact (MorphismProperty.transfiniteCompositions_monotone
    ((MorphismProperty.pushouts_monotone (trivialFibrations C).llp.coproducts_le).trans
      (trivialFibrations C).llp.pushouts_le)).trans
    (trivialFibrations C).llp.transfiniteCompositions_le

lemma cofibrations_le_objectwise :
    let := modelCategory K I J
    cofibrations (K ⥤ C) ≤ objectwise K (cofibrations C) := by
  let := modelCategory K I J
  have := modelCategory_generated K I J
  change cofibrations (K ⥤ C) ≤ objectwise K (cofibrations C)
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated (generators K I) (generators K J),
    MorphismProperty.llp_rlp_of_hasSmallObjectArgument]
  refine (MorphismProperty.retracts_le_iff
    (P := Quillen.relativeCells.{w} (generators K I))
    (Q := objectwise K (cofibrations C))).mpr ?_
  intro A B f hf l
  have : PreservesColimitsOfSize.{w,w} (evaluation K (C := C) l) :=
    { preservesColimitsOfShape := by intros; infer_instance }
  have h := ModelGeneration.relativeCells_map_le (evaluation K l) _ (cofibrations C)
    (freeGenerators_cofibrations K I J l) f hf
  exact cofibration_cells ((evaluation K l).map f) h

lemma cofibration_app {F G : K ⥤ C} (f : F ⟶ G)
    (hf : let := modelCategory K I J; Cofibration f) (k : K) : Cofibration (f.app k) := by
  let := modelCategory K I J
  exact ⟨cofibrations_le_objectwise K I J f ((cofibration_iff f).mp hf) k⟩

lemma isCofibrant_obj (F : K ⥤ C)
    (hF : let := modelCategory K I J; IsCofibrant F) (k : K) : IsCofibrant (F.obj k) := by
  let := modelCategory K I J
  have := hF
  have h := cofibration_app K I J (initial.to F) inferInstance k
  exact (isCofibrant_iff_of_isInitial ((initial.to F).app k)
    (initialIsInitial.isInitialObj ((CategoryTheory.evaluation K C).obj k)
      (⊥_ (K ⥤ C)))).mpr h

end SerrePositivity.DiagramModel.Projective
