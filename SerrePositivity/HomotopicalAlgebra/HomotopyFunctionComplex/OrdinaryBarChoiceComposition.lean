module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies

/-! # Composition of entire relative extension spaces over the original base action

Composition preserves the fixed boundary in every parameter. The parameter
families satisfy exact unit and associativity laws and determine actual maps
of simplicial choice spaces. Chosen points need not preserve composition.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceComposition
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

lemma composite_boundary {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g) :
    unit hcof hfib a ▷ T ≫ ParameterComposition.comp
        (RelativeChoiceSpace.family _ _ s) (RelativeChoiceSpace.family _ _ t) =
      ParameterComposition.const T (boundary hcof hfib (f ≫ g)) := by
  rw [ParameterComposition.pre_comp, RelativeChoiceSpace.family_boundary_const]
  change ParameterComposition.comp
    (ParameterComposition.const T (OrdinaryKanBarMappingClasses.functor.map f ≫ unit hcof hfib b))
    (RelativeChoiceSpace.family _ _ t) = _
  rw [ParameterComposition.const_comp_family, comp_whiskerRight, Category.assoc,
    RelativeChoiceSpace.family_boundary_const]
  unfold boundary
  rw [OrdinaryKanBarMappingClasses.functor.map_comp]
  ext n x
  rfl

def compose {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g) :
    T ⟶ choices hcof hfib (f ≫ g) :=
  RelativeChoiceSpace.ofFamily _ _ (ParameterComposition.comp
    (RelativeChoiceSpace.family _ _ s) (RelativeChoiceSpace.family _ _ t))
    (composite_boundary hcof hfib f g s t)

lemma compose_family {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g) :
    RelativeChoiceSpace.family _ _ (compose hcof hfib f g s t) =
      ParameterComposition.comp (RelativeChoiceSpace.family _ _ s)
        (RelativeChoiceSpace.family _ _ t) :=
  RelativeChoiceSpace.ofFamily_family _ _ _ _

lemma compose_naturality {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c)
    {T U : SSet.{max u v}} (j : U ⟶ T)
    (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g) :
    compose hcof hfib f g (j ≫ s) (j ≫ t) = j ≫ compose hcof hfib f g s t := by
  apply RelativeChoiceSpace.family_injective
  rw [compose_family, RelativeChoiceSpace.family_naturality,
    RelativeChoiceSpace.family_naturality, RelativeChoiceSpace.family_naturality, compose_family]
  exact (ParameterComposition.substitute_comp j _ _).symm

def identity (b : Cᵒᵖ × C) (T : SSet.{max u v}) : T ⟶ choices hcof hfib (𝟙 b) :=
  RelativeChoiceSpace.ofFamily _ _ (ParameterComposition.const T (𝟙 (ambient hcof hfib b)))
    (by
      simp only [boundary, OrdinaryKanBarMappingClasses.functor.map_id, Category.id_comp]
      ext n x
      rfl)

lemma identity_family (b : Cᵒᵖ × C) (T : SSet.{max u v}) :
    RelativeChoiceSpace.family _ _ (identity hcof hfib b T) =
      ParameterComposition.const T (𝟙 (ambient hcof hfib b)) :=
  RelativeChoiceSpace.ofFamily_family _ _ _ _

lemma left_unit_family {a b : Cᵒᵖ × C} (f : a ⟶ b)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) :
    RelativeChoiceSpace.family _ _ (compose hcof hfib (𝟙 a) f (identity hcof hfib a T) s) =
      RelativeChoiceSpace.family _ _ s := by
  rw [compose_family, identity_family, ParameterComposition.id_comp]

lemma right_unit_family {a b : Cᵒᵖ × C} (f : a ⟶ b)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) :
    RelativeChoiceSpace.family _ _ (compose hcof hfib f (𝟙 b) s (identity hcof hfib b T)) =
      RelativeChoiceSpace.family _ _ s := by
  rw [compose_family, identity_family, ParameterComposition.comp_id]

lemma associativity_family {a b c d : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g)
    (r : T ⟶ choices hcof hfib h) :
    RelativeChoiceSpace.family _ _
        (compose hcof hfib (f ≫ g) h (compose hcof hfib f g s t) r) =
      RelativeChoiceSpace.family _ _
        (compose hcof hfib f (g ≫ h) s (compose hcof hfib g h t r)) := by
  simp only [compose_family, ParameterComposition.assoc]

def composition {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) :
    choices hcof hfib f ⊗ choices hcof hfib g ⟶ choices hcof hfib (f ≫ g) :=
  compose hcof hfib f g (fst _ _) (snd _ _)

lemma composition_pair {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g) :
    lift s t ≫ composition hcof hfib f g = compose hcof hfib f g s t := by
  rw [composition, ← compose_naturality]
  simp only [lift_fst, lift_snd]

def relabel {a b : Cᵒᵖ × C} {f g : a ⟶ b} (e : f = g) :
    choices hcof hfib f ⟶ choices hcof hfib g :=
  eqToHom (congrArg (choices hcof hfib) e)

lemma relabel_family {a b : Cᵒᵖ × C} {f g : a ⟶ b} (e : f = g)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) :
    RelativeChoiceSpace.family _ _ (s ≫ relabel hcof hfib e) =
      RelativeChoiceSpace.family _ _ s := by
  subst e
  rfl

lemma left_unit {a b : Cᵒᵖ × C} (f : a ⟶ b)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) :
    compose hcof hfib (𝟙 a) f (identity hcof hfib a T) s ≫
        relabel hcof hfib (Category.id_comp f) = s := by
  apply RelativeChoiceSpace.family_injective
  rw [relabel_family, left_unit_family]

lemma right_unit {a b : Cᵒᵖ × C} (f : a ⟶ b)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) :
    compose hcof hfib f (𝟙 b) s (identity hcof hfib b T) ≫
        relabel hcof hfib (Category.comp_id f) = s := by
  apply RelativeChoiceSpace.family_injective
  rw [relabel_family, right_unit_family]

lemma associativity {a b c d : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g)
    (r : T ⟶ choices hcof hfib h) :
    compose hcof hfib (f ≫ g) h (compose hcof hfib f g s t) r ≫
        relabel hcof hfib (Category.assoc f g h) =
      compose hcof hfib f (g ≫ h) s (compose hcof hfib g h t r) := by
  apply RelativeChoiceSpace.family_injective
  rw [relabel_family, associativity_family]

lemma compose_actionPoint {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) :
    compose hcof hfib f g (actionPoint hcof hfib f) (actionPoint hcof hfib g) =
      compositePoint hcof hfib f g := by
  apply RelativeChoiceSpace.family_injective
  rw [compose_family]
  simp only [actionPoint, compositePoint, RelativeChoiceSpace.family_ofExtension_const,
    ParameterComposition.const_comp]

def compositeComparison {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (unit hcof hfib a)
      (boundary hcof hfib (f ≫ g)) (action hcof hfib (f ≫ g))
      (action hcof hfib f ≫ action hcof hfib g) :=
  (LocalizedRelativeChoice.nonempty_fixedBoundaryHomotopy _
    (unit_localized_isIso hcof hfib a) (ambient_kan hcof hfib c) _ _ _
    (action_fac hcof hfib (f ≫ g)) (composite_fac hcof hfib f g)).some

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceComposition
