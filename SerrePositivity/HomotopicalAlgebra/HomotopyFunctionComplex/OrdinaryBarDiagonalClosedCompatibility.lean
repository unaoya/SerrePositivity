module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition

/-! # The whole diagonal mapping preserves standard composition and native families -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarDiagonalAction
open OrdinaryBarDiagonalClosedAction
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

lemma mapping_nativeFamily {T : SSet.{v}} {X Y : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    lift j f ≫ mapping hcof hfib P X Y =
      UniverseLift.map.{max u v} (nativeFamily hcof hfib P j f) := by
  have h := UniverseLiftClosedCurry.curry_lowerTensor (largeFamily hcof hfib P j f)
  rw [lower_largeFamily] at h
  rw [mapping_family, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

lemma mapping_comp {T : SSet.{max u v}} {X Y Z : D C} (j : T ⟶ P)
    (f : T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    lift j (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) ≫
        mapping hcof hfib P X Z =
      lift (lift j f ≫ mapping hcof hfib P X Y) (lift j g ≫ mapping hcof hfib P Y Z) ≫
        UniverseLiftClosedComposition.liftedComposition.{max u v}
          (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z) := by
  rw [mapping_family, mapping_family, mapping_family, ← largeFamily_comp,
    ClosedParameterComposition.curry_comp, Category.assoc]
  rw [← UniverseLiftClosedComposition.inverse_composition, ← Category.assoc]
  congr 1

lemma mapping_identity {T : SSet.{max u v}} (X : D C) (j : T ⟶ P) :
    lift j (SSet.stdSimplex.isTerminalObj₀.from T ≫
      OrdinaryBarFixedWordResolution.identity C X) ≫ mapping hcof hfib P X X =
        UniverseLiftClosedComposition.unitFrom (small hcof hfib X) T := by
  rw [mapping_family, largeFamily_identity, ClosedParameterComposition.curry_fst,
    UniverseLiftClosedComposition.unitFrom_eq, Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility
