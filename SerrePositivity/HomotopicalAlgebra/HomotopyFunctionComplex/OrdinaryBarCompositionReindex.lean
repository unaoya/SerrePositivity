module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport

/-! # Actual reindexing of the small composition triangle choice space -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T U : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z) (i : U ⟶ T)

lemma compositeComparison_reindex :
    curry (nativeRestrictionComparison hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e).h ≫
      (pre i).app ((ihom (small hcof hfib X)).obj (small hcof hfib Z)) =
    curry (nativeRestrictionComparison hcof hfib P (UniverseLift.map i ≫ j)
      (lift (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g) ≫
        OrdinaryBarFixedWordResolution.composition C X Y Z) (UniverseLift.map i ≫ e)).h := by
  rw [curry_pre_app]
  have h := nativeRestrictionComparison_substitute hcof hfib P j
    (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e i
  have he : UniverseLift.map.{max u v} i ≫
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) =
    lift (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g) ≫
      OrdinaryBarFixedWordResolution.composition C X Y Z := by rw [← Category.assoc, comp_lift]
  rw [he] at h
  rw [h]

lemma inputComparison_reindex : curry (compositionComparison hcof hfib P j f g c d).h ≫
      (pre i).app ((ihom (small hcof hfib X)).obj (small hcof hfib Z)) =
    curry (compositionComparison hcof hfib P (UniverseLift.map i ≫ j)
      (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
      (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)).h := by
  rw [curry_pre_app, compositionComparison_substitute]

def compositionChoices_reindex : compositionChoices hcof hfib P j f g c d e ⟶
    compositionChoices hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
      (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)
      (UniverseLift.map i ≫ e) :=
  ComparisonTriangleTransport.map _ _ _ _ ((pre i).app _)
    (compositeComparison_reindex hcof hfib P j f g e i)
    (inputComparison_reindex hcof hfib P j f g c d i)

def compositionTriangle_reindex (a : compositionTriangleData hcof hfib P j f g c d e) :
    compositionTriangleData hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
      (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)
      (UniverseLift.map i ≫ e) :=
  ComparisonTriangleTransport.data _ _ _ _ ((pre i).app _)
    (compositeComparison_reindex hcof hfib P j f g e i)
    (inputComparison_reindex hcof hfib P j f g c d i) a

lemma compositionChoiceFamily_reindex {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    compositionChoiceFamily hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
      (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)
      (UniverseLift.map i ≫ e) (q ≫ compositionChoices_reindex hcof hfib P j f g c d e i) =
    i ▷ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ≫
      compositionChoiceFamily hcof hfib P j f g c d e q := by
  rw [compositionChoiceFamily, compositionChoices_reindex, ComparisonTriangleTransport.family_map,
    uncurry_pre_app]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
