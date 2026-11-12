module

public import SerrePositivity.HomotopicalAlgebra.Localization.Bifunctor
public import SerrePositivity.HomotopicalAlgebra.Localization.MonoidalUnit
public import SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorSymmetrize
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # Monoidal compatibility of an actual localization

For a braided closed monoidal source, generating cofibrations with
cofibrant domains and derived tensor compatibility at their endpoints
imply the pushout-product axiom in both localized variables. The separate
unit axiom is inherited from the original model, without a cofibrant unit.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.IsLocalizationModel
variable {C : Type u} [Category.{v} C] [original : ModelCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [simplicial : ModelCategory SSet.{v}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S : MorphismProperty C} {m : ModelCategory C}
  (h : @IsLocalizationModel C _ original simplicial cof fib S m)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{v}.rlp)
  (I J G : MorphismProperty C)
  [@_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} C _ original I J]
  [@_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} C _ m I G]

include h hcof hfib I J G in
lemma monoidal_model_of_tensor_compatible
    (hF : @Quillen.IsQuillenBifunctor C _ original C _ original C _ original (curriedTensor C))
    (hu : @Quillen.HasUnitAxiom C _ original _)
    (hdom : let := original; ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)
    (hcompat : ∀ {A B : C} (i : A ⟶ B), I i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      (@localEquivalences C _ original simplicial cof fib S)
        (((curriedTensor C).obj A).map ((@cofibrantSource C _ original cof).map s)) ∧
      (@localEquivalences C _ original simplicial cof fib S)
        (((curriedTensor C).obj B).map ((@cofibrantSource C _ original cof).map s))) :
    @Quillen.MonoidalModelCategory C _ m _ := by
  let := original
  let adj := MonoidalClosed.internalHomAdjunction₂ (C := C)
  let adjFlip := ParametrizedAdjunctionTransport.left adj (BraidedCategory.curriedBraidingNatIso C)
  have hone := h.bifunctor_of_tensor_compatible (base := original) hcof hfib adj adjFlip
    hF I J I G hdom hcompat
  have hboth := Quillen.isQuillenBifunctor_change_both_of_commutor original m h.cofibrations_eq
    (BraidedCategory.curriedBraidingNatIso C) hone
  have hunit := h.hasUnitAxiom hcof hu
  exact @Quillen.MonoidalModelCategory.mk C _ m _ hboth hunit

end SerrePositivity.Bousfield.IsLocalizationModel
