module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RestrictionDescentChoices

/-! # Relative descent choices for the actual whole word action

The same global comparison interval supplies every parameter family.
Prescribed boundaries extend strictly in this choice space. Native
parameter evaluations still land in the original small internal Hom.
-/

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
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev parameterAugmentation (X Y : D C) := P ◁ smallAugmentation C X Y

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma parameterAugmentation_isIso (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (parameterAugmentation P X Y)) :=
  AnodyneHomotopy.whiskerLeft_anodyneQ_isIso _
    (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y) P

abbrev choices (X Y : D C) : SSet.{max u v} :=
  RestrictionDescentChoices.obj (parameterAugmentation P X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)

lemma choices_boundary_rlp (X Y : D C) : SSet.modelCategoryQuillen.I.rlp
    (terminal.from (choices hcof hfib P X Y)) :=
  RestrictionDescentChoices.boundary_rlp _ _

lemma choices_kan (X Y : D C) : SSet.modelCategoryQuillen.J.rlp
    (terminal.from (choices hcof hfib P X Y)) :=
  RestrictionDescentChoices.kan _ _

def family {T : SSet.{max u v}} {X Y : D C} (c : T ⟶ choices hcof hfib P X Y) :
    (P ⊗ baseHom C X Y) ⊗ T ⟶
      UniverseLift.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  RestrictionDescentChoices.family (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c

lemma family_naturality {T U : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) (j : U ⟶ T) :
    family hcof hfib P (j ≫ c) = (P ⊗ baseHom C X Y) ◁ j ≫ family hcof hfib P c :=
  RestrictionDescentChoices.family_naturality _ _ _ _ _ _

abbrev comparison {T : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) :=
  RestrictionDescentChoices.parameterComparison (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c

abbrev familyComparison {T : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) :=
  RestrictionDescentChoices.familyComparison (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c

lemma comparison_naturality {T U : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) (j : U ⟶ T) :
    (comparison hcof hfib P (j ≫ c)).h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (comparison hcof hfib P c).h :=
  RestrictionDescentChoices.parameterComparison_naturality _ _ _ _ _ _

lemma relative_extension {U V : SSet.{max u v}} {X Y : D C} (j : U ⟶ V) [Mono j]
    (c : U ⟶ choices hcof hfib P X Y) : ∃ e : V ⟶ choices hcof hfib P X Y,
      j ≫ e = c ∧ (P ⊗ baseHom C X Y) ◁ j ≫ family hcof hfib P e = family hcof hfib P c ∧
        j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (comparison hcof hfib P e).h = (comparison hcof hfib P c).h :=
  RestrictionDescentChoices.relative_extension _ _ _ _ _ _

def nativeFamily {T : SSet.{v}} {X Y : D C} (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ baseHom C X Y)
    (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y) :
    T ⟶ (ihom (small hcof hfib X)).obj (small hcof hfib Y) :=
  UniverseLift.lower (lift (lift j f) (𝟙 _) ≫ family hcof hfib P c)

lemma nativeFamily_substitute {T U : SSet.{v}} {X Y : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ baseHom C X Y)
    (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y) (i : U ⟶ T) :
    nativeFamily hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
        (UniverseLift.map i ≫ c) = i ≫ nativeFamily hcof hfib P j f c := by
  apply (SSet.uliftFunctor.{max u v, v}).map_injective
  change lift (lift (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)) (𝟙 _) ≫
      family hcof hfib P (UniverseLift.map i ≫ c) =
    UniverseLift.map i ≫ lift (lift j f) (𝟙 _) ≫ family hcof hfib P c
  rw [family_naturality, ← Category.assoc, lift_whiskerLeft]
  rw [Category.id_comp, ← Category.assoc, comp_lift, comp_lift, Category.comp_id]

lemma native_relative_extension {U V : SSet.{v}} {X Y : D C} (i : U ⟶ V) [Mono i]
    (j : UniverseLift.obj.{max u v} V ⟶ P)
    (f : UniverseLift.obj.{max u v} V ⟶ baseHom C X Y)
    (c : UniverseLift.obj.{max u v} U ⟶ choices hcof hfib P X Y) :
    ∃ e : UniverseLift.obj.{max u v} V ⟶ choices hcof hfib P X Y,
      UniverseLift.map i ≫ e = c ∧ i ≫ nativeFamily hcof hfib P j f e =
        nativeFamily hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) c := by
  have : Mono (UniverseLift.map.{max u v} i) := UniverseLift.mono_map i
  obtain ⟨e, he, _, _⟩ := relative_extension hcof hfib P (UniverseLift.map i) c
  refine ⟨e, he, ?_⟩
  rw [← nativeFamily_substitute, he]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
