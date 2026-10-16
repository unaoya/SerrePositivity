module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RetractChainUnits

/-! # Actual endpoint units and unit-boundary formulas for all free-resolution degrees

The strong contraction equations are proved by the existing retract system.
All contraction parameters stay arbitrary in the endpoint unit formulas.
The original interval action is not assumed to be a strict monoid action.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarFreeChainTransfer
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {U : SSet.{max u v}} (j : U ⟶ parameters P n)

abbrev parameterContraction (X : D C) (t : U ⟶ RetractChainFamily.interval) :=
  RetractChainFamily.contraction (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) X t

lemma parameterContraction_zero (X : D C) :
    parameterContraction hcof hfib X (RetractChainFamily.zero U) =
      ParameterComposition.const U (𝟙 (ambient hcof hfib X)) :=
  RetractChainFamily.contraction_zero _ _ _ _ _ X U

lemma parameterContraction_one_right (X : D C) (t : U ⟶ RetractChainFamily.interval) :
    ParameterComposition.comp (parameterContraction hcof hfib X t)
      (parameterContraction hcof hfib X (RetractChainFamily.one U)) =
        parameterContraction hcof hfib X (RetractChainFamily.one U) :=
  RetractChainUnits.contraction_one_right (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) X t

lemma parameterContraction_one_left (X : D C) (t : U ⟶ RetractChainFamily.interval) :
    ParameterComposition.comp (parameterContraction hcof hfib X (RetractChainFamily.one U))
      (parameterContraction hcof hfib X t) =
        parameterContraction hcof hfib X (RetractChainFamily.one U) :=
  RetractChainUnits.contraction_one_left (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_on_section hcof hfib) X t

lemma trailing_identity {a : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (t : U ⟶ RetractChainFamily.interval) :
    OrdinaryBarChainFamily.family hcof hfib
      (snoc hcof hfib P n j q (FreeGeneratorCategories.identity (D C) (n + 1) X) t) =
      OrdinaryBarChainFamily.family hcof hfib q := by
  rw [snoc, OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.trailing_identity (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib) q t

lemma leading_identity {b : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib U X b) (t : U ⟶ RetractChainFamily.interval) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (.nil : chain hcof hfib U X X)
        (FreeGeneratorCategories.identity (D C) (n + 1) X) t).append q) =
      OrdinaryBarChainFamily.family hcof hfib q := by
  rw [snoc, OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.leading_identity (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_on_section hcof hfib) q t

lemma interior_identity_after_zero {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (f : X ⟶ Y) (t : U ⟶ RetractChainFamily.interval)
    (r : chain hcof hfib U Y d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q f (RetractChainFamily.zero U))
        (FreeGeneratorCategories.identity (D C) (n + 1) Y) t).append r) =
      OrdinaryBarChainFamily.family hcof hfib ((snoc hcof hfib P n j q f t).append r) := by
  unfold snoc
  rw [OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.interior_identity_after_zero (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) q _ t r

lemma interior_identity_at_zero {a d : D C} {X Y : degree (D C) (n + 1)}
    (q : chain hcof hfib U a X) (g : X ⟶ Y) (t : U ⟶ RetractChainFamily.interval)
    (r : chain hcof hfib U Y d) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (snoc hcof hfib P n j q
        (FreeGeneratorCategories.identity (D C) (n + 1) X)
        (RetractChainFamily.zero U)) g t).append r) =
      OrdinaryBarChainFamily.family hcof hfib ((snoc hcof hfib P n j q g t).append r) := by
  unfold snoc
  rw [OrdinaryBarFreeAmbientFamilies.family_id, ParameterComposition.substitute_const]
  exact RetractChainUnits.interior_identity_at_zero (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) q _ t r

lemma small_trailing_identity {T : SSet.{v}}
    (k : UniverseLift.obj.{max u v} T ⟶ parameters P n) {a : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib (UniverseLift.obj.{max u v} T) a X)
    (t : UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
      (snoc hcof hfib P n k q (FreeGeneratorCategories.identity (D C) (n + 1) X) t) =
      OrdinaryBarChainFamily.smallFamily hcof hfib q :=
  congrArg UniverseLift.lowerTensor (trailing_identity hcof hfib P n k q t)

lemma small_leading_identity {T : SSet.{v}}
    (k : UniverseLift.obj.{max u v} T ⟶ parameters P n) {b : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib (UniverseLift.obj.{max u v} T) X b)
    (t : UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
      ((snoc hcof hfib P n k (.nil : chain hcof hfib (UniverseLift.obj.{max u v} T) X X)
        (FreeGeneratorCategories.identity (D C) (n + 1) X) t).append q) =
      OrdinaryBarChainFamily.smallFamily hcof hfib q :=
  congrArg UniverseLift.lowerTensor (leading_identity hcof hfib P n k q t)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits
