module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex

/-! # Identity, composition, and selected-point laws for composition-choice reindexing -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T U V : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z)

lemma compositionChoices_reindex_id : compositionChoices_reindex hcof hfib P j f g c d e (𝟙 T) =
    𝟙 (compositionChoices hcof hfib P j f g c d e) := by
  unfold compositionChoices_reindex
  simp only [pre_id, NatTrans.id_app]
  exact ComparisonTriangleTransport.map_id _ _

lemma compositionChoices_reindex_comp (i : U ⟶ T) (k : V ⟶ U) :
    compositionChoices_reindex hcof hfib P j f g c d e i ≫
      compositionChoices_reindex hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
        (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)
        (UniverseLift.map i ≫ e) k =
    compositionChoices_reindex hcof hfib P j f g c d e (k ≫ i) := by
  apply pullback.hom_ext
  · simp only [compositionChoices_reindex, ComparisonTriangleTransport.map, Category.assoc,
      RelativeChoiceSpace.postMap_inclusion, RelativeChoiceSpace.postMap_inclusion_assoc]
    rw [← (ihom (SSet.stdSimplex.obj (SimplexCategory.mk 2))).map_comp]
    have hq : (pre i).app ((ihom (small hcof hfib X)).obj (small hcof hfib Z)) ≫
        (pre k).app _ = (pre (k ≫ i)).app _ := RelativeChoiceSpace.restriction_comp k i
    rw [hq]
  · simp only [compositionChoices_reindex, ComparisonTriangleTransport.map, Category.assoc,
      RelativeChoiceSpace.postMap_projection]

variable (i : U ⟶ T)

lemma compositionTriangle_point_reindex (a : compositionTriangleData hcof hfib P j f g c d e) :
    ComparisonTriangleChoices.ofData _ _ a ≫
        compositionChoices_reindex hcof hfib P j f g c d e i =
      ComparisonTriangleChoices.ofData _ _
        (compositionTriangle_reindex hcof hfib P j f g c d e i a) :=
  ComparisonTriangleTransport.ofData_map _ _ _ _ _ _ _ _

lemma compositionTriangle_family_reindex (a : compositionTriangleData hcof hfib P j f g c d e) :
    uncurry (compositionTriangle_reindex hcof hfib P j f g c d e i a).triangle =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ uncurry a.triangle := by
  change uncurry (a.triangle ≫ (pre i).app _) = _
  rw [uncurry_pre_app]

abbrev selectedTriangleReindexComparison := comparisonOfCompositionTriangles hcof hfib P
  (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
  (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d) (UniverseLift.map i ≫ e)
  (compositionTriangle_reindex hcof hfib P j f g c d e i
    (compositionTriangle hcof hfib P j f g c d e))
  (compositionTriangle hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
    (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)
    (UniverseLift.map i ≫ e))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
