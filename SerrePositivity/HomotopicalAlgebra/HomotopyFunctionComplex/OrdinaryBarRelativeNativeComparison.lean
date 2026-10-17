module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation

/-! # Native interval comparisons decoded from the relative descent space

The comparison is an actual homotopy between maps into the original
small internal Hom, extracted from the one global comparison interval.
-/

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
  (P : SSet.{max u v})

def nativeRestrictionComparison {T : SSet.{v}} {X Y : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y) :
    SSet.Homotopy (nativeFamily hcof hfib P j (g ≫ smallAugmentation C X Y) c)
      (OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j g) := by
  let H := RestrictionDescentChoices.fixedFamilyComparison (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c
  let W := HomotopyClasses.preHomotopy (lift (lift j g) (𝟙 _)) H
  apply UniverseLift.lowerHomotopy
  refine LargeParameterSquare.changeEndpoints W ?_ ?_
  · change lift (lift j g) (𝟙 _) ≫ parameterAugmentation P X Y ▷ _ ≫
        family hcof hfib P c = _
    rw [← Category.assoc, lift_whiskerRight, lift_whiskerLeft]
    rfl
  · change lift (lift j g) (𝟙 _) ≫ fst _ _ ≫
      OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y = _
    rw [← Category.assoc, lift_fst,
      OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily]

lemma nativeRestrictionComparison_substitute {T U : SSet.{v}} {X Y : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y) (i : U ⟶ T) :
    (nativeRestrictionComparison hcof hfib P (UniverseLift.map i ≫ j)
      (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c)).h =
        i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (nativeRestrictionComparison hcof hfib P j g c).h := by
  ext n x
  simp only [nativeRestrictionComparison, UniverseLift.lowerHomotopy,
    LargeParameterSquare.changeEndpoints_h, RestrictionDescentChoices.fixedFamilyComparison,
    RestrictionDescentChoices.familyComparison, RestrictionDescentChoices.parameterComparison,
    HomotopyClassesClosed.uncurryHomotopy, HomotopyClasses.preHomotopy,
    UniverseLift.lowerSimplexTensor]
  rfl

lemma native_relative_comparison_extension {U V : SSet.{v}} {X Y : D C} (i : U ⟶ V) [Mono i]
    (j : UniverseLift.obj.{max u v} V ⟶ P)
    (g : UniverseLift.obj.{max u v} V ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (c : UniverseLift.obj.{max u v} U ⟶ choices hcof hfib P X Y) :
    ∃ e : UniverseLift.obj.{max u v} V ⟶ choices hcof hfib P X Y,
      UniverseLift.map i ≫ e = c ∧
        i ≫ nativeFamily hcof hfib P j (g ≫ smallAugmentation C X Y) e =
          nativeFamily hcof hfib P (UniverseLift.map i ≫ j)
            ((UniverseLift.map i ≫ g) ≫ smallAugmentation C X Y) c ∧
        i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (nativeRestrictionComparison hcof hfib P j g e).h =
            (nativeRestrictionComparison hcof hfib P (UniverseLift.map i ≫ j)
              (UniverseLift.map i ≫ g) c).h := by
  obtain ⟨e, he, hf⟩ := native_relative_extension hcof hfib P i j
    (g ≫ smallAugmentation C X Y) c
  refine ⟨e, he, ?_, ?_⟩
  · simpa only [Category.assoc] using hf
  · rw [← nativeRestrictionComparison_substitute, he]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
