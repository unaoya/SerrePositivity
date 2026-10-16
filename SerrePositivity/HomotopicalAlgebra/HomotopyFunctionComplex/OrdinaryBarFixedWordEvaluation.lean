module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators

/-! # Every ordinary simplex map commutes with the actual fixed-object word evaluation -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
open OrdinaryBarRetractSystem OrdinaryBarWordPresentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

lemma evaluation_map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (k : SimplexCategoryᵒᵖ)
    (t : (OrdinaryBarFreeResolutionAction.parameters P m).obj k) :
    RetractWords.map (literalMap C θ)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      largeEvaluation (C := C) hcof hfib P m.unop.len k t =
    largeEvaluation (C := C) hcof hfib P n.unop.len k
      ((P ◁ SSet.stdSimplex.map θ.unop).app k t) := by
  apply RetractWords.functor_ext_generators
    (C := degree (D C) (n.unop.len + 1)) (M := WordSegment.degree.{max u v} k)
  · rintro ⟨X⟩
    cases X <;> rfl
  · intro X Y e
    change RetractWords.Edge _ _ X Y at e
    cases e with
    | source f =>
      simp only [CategoryTheory.Functor.comp_map,
        RetractWords.Realization.functor_source]
      apply heq_of_eq
      apply ConcreteCategory.hom_ext
      intro x
      change ((OrdinaryBarFixedChoices.action hcof hfib P m).map
        ((literalMap C θ).map f)).app k (x, t) =
          ((OrdinaryBarFixedChoices.action hcof hfib P n).map f).app k
            (x, (P ◁ SSet.stdSimplex.map θ.unop).app k t)
      have h := congr($(OrdinaryBarFixedChoices.action_naturality
        (C := C) hcof hfib P θ).map f)
      exact types_congr_hom (congr_app h k) (x, t)
    | word X w =>
      simp only [CategoryTheory.Functor.comp_map,
        RetractWords.Realization.functor_word]
      rfl
    | section_ X =>
      simp only [CategoryTheory.Functor.comp_map,
        RetractWords.Realization.functor_section]
      rfl
    | projection X =>
      simp only [CategoryTheory.Functor.comp_map,
        RetractWords.Realization.functor_projection]
      rfl

lemma family_map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {T : SSet.{v}}
    (j : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFreeResolutionAction.parameters P m)
    {X Y : D C}
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarWordAction.hom (C := C) n.unop.len X Y) :
    OrdinaryBarWordAction.family hcof hfib P m.unop.len j
      (f ≫ WordPresentationSourceMap.mapHomSame (literalMap C θ) X Y) =
    OrdinaryBarWordAction.family hcof hfib P n.unop.len
      (j ≫ P ◁ SSet.stdSimplex.map θ.unop) f := by
  ext k x
  have he := congr($(evaluation_map (C := C) hcof hfib P θ k
    (j.app k (ULift.up x.2))).map (f.app k (ULift.up x.2)))
  exact congrArg ULift.down (types_congr_hom he (ULift.up x.1))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation
