module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition

/-! # Two selected native comparisons compose through one specified square -/

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
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)

abbrev compositionSquare : (T ⊗ HomotopyBinarySquare.interval) ⊗
    HomotopyBinarySquare.interval ⟶ (ihom (small hcof hfib X)).obj (small hcof hfib Z) :=
  ClosedHomotopyComposition.square (nativeRestrictionComparison hcof hfib P j f c)
    (nativeRestrictionComparison hcof hfib P j g d)

def compositionComparison : SSet.Homotopy
    (lift (nativeFamily hcof hfib P j (f ≫ smallAugmentation C X Y) c)
      (nativeFamily hcof hfib P j (g ≫ smallAugmentation C Y Z) d) ≫
        MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z))
    (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z)) :=
  LargeParameterSquare.changeEndpoints
    (ClosedHomotopyComposition.comp (nativeRestrictionComparison hcof hfib P j f c)
      (nativeRestrictionComparison hcof hfib P j g d)) rfl
    (OrdinaryBarDiagonalClosedAction.nativeFamily_comp hcof hfib P j f g).symm

lemma compositionSquare_outer_zero : SSet.ι₀ ≫ compositionSquare hcof hfib P j f g c d =
    lift (nativeRestrictionComparison hcof hfib P j f c).h
      (fst T HomotopyBinarySquare.interval ≫
        nativeFamily hcof hfib P j (g ≫ smallAugmentation C Y Z) d) ≫
      MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) :=
  HomotopyBinarySquare.square_outer_zero _ _ _

lemma compositionSquare_outer_one : SSet.ι₁ ≫ compositionSquare hcof hfib P j f g c d =
    lift (nativeRestrictionComparison hcof hfib P j f c).h
      (fst T HomotopyBinarySquare.interval ≫
        OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j g) ≫
      MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) :=
  HomotopyBinarySquare.square_outer_one _ _ _

lemma compositionSquare_inner_zero : (SSet.ι₀ (X := T)) ▷ HomotopyBinarySquare.interval ≫
    compositionSquare hcof hfib P j f g c d =
      lift (fst T HomotopyBinarySquare.interval ≫
        nativeFamily hcof hfib P j (f ≫ smallAugmentation C X Y) c)
        (nativeRestrictionComparison hcof hfib P j g d).h ≫
      MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) :=
  HomotopyBinarySquare.square_inner_zero _ _ _

lemma compositionSquare_inner_one : (SSet.ι₁ (X := T)) ▷ HomotopyBinarySquare.interval ≫
    compositionSquare hcof hfib P j f g c d =
      lift (fst T HomotopyBinarySquare.interval ≫
        OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j f)
        (nativeRestrictionComparison hcof hfib P j g d).h ≫
      MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) :=
  HomotopyBinarySquare.square_inner_one _ _ _

lemma compositionSquare_diagonal : HomotopyBinarySquare.diagonal T ≫
    compositionSquare hcof hfib P j f g c d = (compositionComparison hcof hfib P j f g c d).h := by
  simp only [compositionComparison, LargeParameterSquare.changeEndpoints_h]
  exact HomotopyBinarySquare.diagonal_square _ _ _

lemma compositionComparison_substitute {U : SSet.{v}} (i : U ⟶ T) :
    (compositionComparison hcof hfib P (UniverseLift.map i ≫ j)
      (UniverseLift.map i ≫ f) (UniverseLift.map i ≫ g)
      (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)).h =
      i ▷ HomotopyBinarySquare.interval ≫ (compositionComparison hcof hfib P j f g c d).h := by
  simp only [compositionComparison, LargeParameterSquare.changeEndpoints_h]
  change lift _ _ ≫ MonoidalClosed.comp _ _ _ = i ▷ _ ≫ (lift _ _ ≫ _)
  rw [nativeRestrictionComparison_substitute, nativeRestrictionComparison_substitute,
    ← Category.assoc, comp_lift]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
