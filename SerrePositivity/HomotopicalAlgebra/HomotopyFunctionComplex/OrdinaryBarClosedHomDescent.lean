module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SplitLocalizedDescent
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom

/-! # Actual descent of each whole parameterized action to the original Hom

These maps land in lifts of the actual small internal Hom, and restriction
recovers the original action up to an actual interval homotopy. This does
not assert strict composition of the descended maps.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

lemma target_kan (X Y : D C) : SSet.modelCategoryQuillen.J.rlp (terminal.from
    (UniverseLift.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)))) :=
  UniverseLift.horn_terminal_map (SimplexParameterHom.native_kan
    (small hcof hfib X) (small hcof hfib Y) (OrdinaryBarSmallReference.value_kan hcof hfib Y))

def mapping (X Y : D C) : P ⊗ baseHom C X Y ⟶
    UniverseLift.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  SplitLocalizedDescent.descend
    (SplitLocalizedDescent.tensorSplit (OrdinaryBarHomSections.small C X Y) P)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)

lemma restriction_homotopy (X Y : D C) : Nonempty (SSet.Homotopy
    ((P ◁ smallAugmentation C X Y) ≫ mapping hcof hfib P X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)) :=
  SplitLocalizedDescent.tensor_descend_homotopy (OrdinaryBarHomSections.small C X Y)
    (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y) P
    (target_kan hcof hfib X Y) (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)

lemma lifts_homotopy {T : SSet.{max u v}} {X Y : D C} (j : T ⟶ P)
    (f g : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (hfg : f ≫ smallAugmentation C X Y = g ≫ smallAugmentation C X Y) :
    Nonempty (SSet.Homotopy
      (lift j f ≫ OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)
      (lift j g ≫ OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)) := by
  have h : lift j f ≫ (P ◁ smallAugmentation C X Y) =
      lift j g ≫ (P ◁ smallAugmentation C X Y) := by
    rw [lift_whiskerLeft, lift_whiskerLeft, hfg]
  exact SplitLocalizedDescent.lifts_homotopy
    (AnodyneHomotopy.whiskerLeft_anodyneQ_isIso _
      (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y) P)
    (target_kan hcof hfib X Y) (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)
    (lift j f) (lift j g) h

lemma native_lifts_homotopy {T : SSet.{v}} {X Y : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (hfg : f ≫ smallAugmentation C X Y = g ≫ smallAugmentation C X Y) :
    Nonempty (SSet.Homotopy
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j f)
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j g)) := by
  obtain ⟨H⟩ := lifts_homotopy hcof hfib P j f g hfg
  have h := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) H
  rw [OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily,
    OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily] at h
  exact (UniverseLift.localized_map_eq_iff_homotopy AnodyneHomotopy.anodyneQ T
    ((ihom (small hcof hfib X)).obj (small hcof hfib Y))
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Y))
    _ _).mp h

def nativeFamily {T : SSet.{v}} {X Y : D C} (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ baseHom C X Y) :
    T ⟶ (ihom (small hcof hfib X)).obj (small hcof hfib Y) :=
  OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j
    (f ≫ (OrdinaryBarHomSections.small C X Y).section_)

lemma nativeFamily_substitute {T U : SSet.{v}} {X Y : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ baseHom C X Y) (i : U ⟶ T) :
    nativeFamily hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) =
      i ≫ nativeFamily hcof hfib P j f := by
  unfold nativeFamily
  rw [Category.assoc, OrdinaryBarDiagonalClosedAction.nativeFamily_substitute]

lemma native_restriction_homotopy {T : SSet.{v}} {X Y : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    Nonempty (SSet.Homotopy
      (nativeFamily hcof hfib P j (f ≫ smallAugmentation C X Y))
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j f)) := by
  apply native_lifts_homotopy hcof hfib P
  rw [Category.assoc, Category.assoc, (OrdinaryBarHomSections.small C X Y).id,
    Category.comp_id]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
