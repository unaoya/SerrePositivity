module

public import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
public import SerrePositivity.HomotopicalAlgebra.Localization.Monoidal

/-! # Actual monoidal localization under derived tensor compatibility

Construct the ordinary localization and its monoidal model compatibility
from the original monoidal model, the stated generating-domain condition
and derived tensor tests. Neither a localized model nor a cofibrant
monoidal unit is an input.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MonoidalCategory

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [original : ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  [simplicialV : ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [hM : Quillen.MonoidalModelCategory C]

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma exists_monoidal_localization (S : MorphismProperty C) [S.IsSmall.{w}]
    (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)
    (hcompat : ∀ {A B : C} (i : A ⟶ B), I i → ∀ {X Y : C} (s : X ⟶ Y), S s →
      localEquivalences.{v, u} (C := C) cof fib S
        (((curriedTensor C).obj A).map ((HomotopyFunctionComplex.cofibrantSource cof).map s)) ∧
      localEquivalences.{v, u} (C := C) cof fib S
        (((curriedTensor C).obj B).map ((HomotopyFunctionComplex.cofibrantSource cof).map s))) :
    ∃ p : ModelPresentation.{w} cof fib I S, @Quillen.MonoidalModelCategory C _ p.model _ := by
  let p := modelPresentation cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S
  let G := p.generators
  have := p.generated
  have hc := p.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  exact ⟨p, hc.monoidal_model_of_tensor_compatible hcofV hfibV I J G
    hM.pushoutProduct hM.unit hdom hcompat⟩

end SerrePositivity.Bousfield
