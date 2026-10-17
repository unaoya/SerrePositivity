module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent

/-! # Parameterized identity and composition homotopies after Hom descent

The maps and the intervals are in the original small value universe.
These are individual comparison intervals, not a coherent strictification.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
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

lemma native_identity_homotopy {T : SSet.{v}} (X : D C)
    (j : UniverseLift.obj.{max u v} T ⟶ P) :
    Nonempty (SSet.Homotopy
      (nativeFamily hcof hfib P j (SSet.stdSimplex.isTerminalObj₀.from _ ≫ baseIdentity C X))
      (toUnit T ≫ MonoidalClosed.id (small hcof hfib X))) := by
  have h := native_restriction_homotopy hcof hfib P j
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C X)
  simpa only [Category.assoc, augmentation_identity,
    OrdinaryBarDiagonalClosedAction.nativeFamily_identity] using h

lemma native_composition_homotopy {T : SSet.{v}} {X Y Z : D C}
    (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ baseHom C X Y)
    (g : UniverseLift.obj.{max u v} T ⟶ baseHom C Y Z) :
    Nonempty (SSet.Homotopy
      (nativeFamily hcof hfib P j (lift f g ≫ baseComposition C X Y Z))
      (lift (nativeFamily hcof hfib P j f) (nativeFamily hcof hfib P j g) ≫
        MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z))) := by
  let f' := f ≫ (OrdinaryBarHomSections.small C X Y).section_
  let g' := g ≫ (OrdinaryBarHomSections.small C Y Z).section_
  let c := lift f' g' ≫ OrdinaryBarFixedWordResolution.composition C X Y Z
  have hc : c ≫ smallAugmentation C X Z = lift f g ≫ baseComposition C X Y Z := by
    dsimp only [c]
    rw [Category.assoc, augmentation_composition, ← Category.assoc, lift_map]
    dsimp only [f', g']
    simp only [Category.assoc, SplitEpi.id, Category.comp_id]
  have h := native_restriction_homotopy hcof hfib P j c
  rw [hc] at h
  dsimp only [c] at h
  rw [OrdinaryBarDiagonalClosedAction.nativeFamily_comp] at h
  exact h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
