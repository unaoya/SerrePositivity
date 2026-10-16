module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution

/-! # Actual diagonal word families evaluated on the native small bar values -/

@[expose] public section
universe v u r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
open OrdinaryBarRetractSystem OrdinaryBarFixedSource

abbrev parameters (P : SSet.{r}) (n : SimplexCategoryᵒᵖ) :=
  OrdinaryBarFreeResolutionAction.parameters P n

def generic (n : SimplexCategoryᵒᵖ) :
    (SSet.stdSimplex.obj n.unop).obj n := SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)

def point {P : SSet.{r}} (n : SimplexCategoryᵒᵖ) (x : P.obj n) : (parameters P n).obj n :=
  (x, generic n)

lemma point_naturality {P : SSet.{r}} {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : P.obj n) :
    (parameters P n).map θ (point n x) =
      (P ◁ SSet.stdSimplex.map θ.unop).app m (point m (P.map θ x)) := by
  rfl

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} (j : UniverseLift.obj.{max u v} T ⟶ P)

abbrev evaluation (n : SimplexCategoryᵒᵖ) (x : P.obj n) :=
  (OrdinaryBarWordPresentation.realization (C := C) hcof hfib P n.unop.len n (point n x)).functor

def family {X Y : D C}
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y where
  app n := ↾fun x =>
    (evaluation hcof hfib P n (j.app n (ULift.up x.2))
      |>.map (f.app n (ULift.up x.2)) (ULift.up x.1)).down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have hj := types_congr_hom (j.naturality θ) (ULift.up x.2)
    change j.app m (ULift.up (T.map θ x.2)) = P.map θ (j.app n (ULift.up x.2)) at hj
    have hf := types_congr_hom (f.naturality θ) (ULift.up x.2)
    change f.app m (ULift.up (T.map θ x.2)) =
      ((OrdinaryBarFixedWordResolution.diagram C).map θ).toFunctor.map
        (f.app n (ULift.up x.2)) at hf
    have hr := congr($(OrdinaryBarFixedWordResolution.map_functor_reverse C θ).map
      (f.app n (ULift.up x.2)))
    rw [hr] at hf
    have he := congr($(OrdinaryBarFixedWordEvaluation.evaluation_map (C := C) hcof hfib P θ m
      (point m (P.map θ (j.app n (ULift.up x.2))))).map
        ((WordPresentationDiagram.smallHom.{u, max u v, max u v}
          (degree (D C) (n.unop.len + 1)) X Y).map θ (f.app n (ULift.up x.2))))
    have hh := WordPresentationNaturality.small_naturality
      (OrdinaryBarFreeAmbientFamilies.fixedAction (C := C) hcof hfib P n.unop.len)
      (lifted (C := C) hcof hfib) (section_ (C := C) hcof hfib)
      (projection (C := C) hcof hfib) (section_fac (C := C) hcof hfib)
      (contraction (C := C) hcof hfib) (contraction_over (C := C) hcof hfib)
      (contraction_on_section (C := C) hcof hfib) θ (point n (j.app n (ULift.up x.2))) X Y
      (f.app n (ULift.up x.2)) (ULift.up x.1)
    rw [point_naturality] at hh
    change (evaluation hcof hfib P m (j.app m (ULift.up (T.map θ x.2))) |>.map
      (f.app m (ULift.up (T.map θ x.2)))
      (ULift.up ((small hcof hfib X).map θ x.1))).down = _
    rw [hj, hf]
    have he' := types_congr_hom he (ULift.up ((small hcof hfib X).map θ x.1))
    exact congrArg ULift.down (he'.trans hh.symm)

lemma family_substitute {U : SSet.{v}} (i : U ⟶ T) {X Y : D C}
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    family hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) =
      ParameterComposition.substitute i (family hcof hfib P j f) := by
  ext n x
  rfl

lemma family_identity (X : D C) :
    family hcof hfib P j
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C X) =
      fst (small hcof hfib X) T := by
  ext n x
  change (evaluation hcof hfib P n (j.app n (ULift.up x.2)) |>.map
    (𝟙 ((RetractWords.quotient (degree (D C) (n.unop.len + 1))
      (WordSegment.degree.{max u v} n)).obj (.small X))) (ULift.up x.1)).down = x.1
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma family_comp {X Y Z : D C}
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    ParameterComposition.comp (family hcof hfib P j f) (family hcof hfib P j g) =
      family hcof hfib P j (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) := by
  ext n x
  change _ = (evaluation hcof hfib P n (j.app n (ULift.up x.2)) |>.map
    (f.app n (ULift.up x.2) ≫ g.app n (ULift.up x.2)) (ULift.up x.1)).down
  rw [CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation
