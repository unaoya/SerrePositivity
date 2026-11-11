module

public import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
public import SerrePositivity.HomotopicalAlgebra.Localization.Iteration

/-! # Existence and comparison of the actual iterated localization

The first localized model supplies its actual generating family, left
properness and functorial model factorizations. Apply the proved general
existence theorem again on that model, and identify the union model as
its T-localization. The iterated localization is not an assumed input.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

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


include J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma ModelPresentation.exists_iterated_certificate {S T : MorphismProperty C} [T.IsSmall.{w}]
    (pS : ModelPresentation.{w} cof fib I S) (pST : ModelPresentation.{w} cof fib I (S ⊔ T)) :
    ∃ (cofS : MorphismProperty.FunctorialFactorizationData
        pS.model.categoryWithCofibrations.cofibrations
        (pS.model.categoryWithFibrations.fibrations ⊓
          pS.model.categoryWithWeakEquivalences.weakEquivalences))
      (fibS : MorphismProperty.FunctorialFactorizationData
        (pS.model.categoryWithCofibrations.cofibrations ⊓
          pS.model.categoryWithWeakEquivalences.weakEquivalences)
        pS.model.categoryWithFibrations.fibrations),
      @IsLocalizationModel C _ pS.model simplicialV cofS fibS T pST.model := by
  have hS := pS.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  have hST := pST.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  let G := pS.generators
  have hgen := pS.generated
  have hleft := pS.leftProper cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  obtain ⟨κ, hκ, ⟨dS⟩⟩ := pS.exists_accessible_factorizations cof fib I
  let := pS.model
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I G := hgen
  have : (weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C) := hleft
  let cofS := dS.cofibrationData
  let fibS := dS.fibrationData
  obtain ⟨pI⟩ := exists_modelPresentation cofS fibS I G IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB T
  have hI := pI.isLocalizationModel cofS fibS I G IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  let := original
  exact ⟨cofS, fibS, union_is_iterated_localization hS hST cofS fibS hI hcofV hfibV⟩


include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma exists_iterated_localization (S T : MorphismProperty C) [S.IsSmall.{w}] [T.IsSmall.{w}] :
    ∃ (pS : ModelPresentation.{w} cof fib I S)
      (pST : ModelPresentation.{w} cof fib I (S ⊔ T)),
      ∃ (cofS : MorphismProperty.FunctorialFactorizationData
          pS.model.categoryWithCofibrations.cofibrations
          (pS.model.categoryWithFibrations.fibrations ⊓
            pS.model.categoryWithWeakEquivalences.weakEquivalences))
        (fibS : MorphismProperty.FunctorialFactorizationData
          (pS.model.categoryWithCofibrations.cofibrations ⊓
            pS.model.categoryWithWeakEquivalences.weakEquivalences)
          pS.model.categoryWithFibrations.fibrations),
        @IsLocalizationModel C _ pS.model simplicialV cofS fibS T pST.model := by
  let U : Bool → MorphismProperty C := fun b => if b then S else T
  have : ∀ b, (U b).IsSmall.{w} := by intro b; cases b <;> dsimp [U] <;> infer_instance
  have he : (⨆ b, U b) = S ⊔ T := by simp [iSup_bool_eq, U]
  have : (S ⊔ T).IsSmall.{w} := he ▸ (inferInstance : (⨆ b, U b).IsSmall.{w})
  obtain ⟨pS⟩ := exists_modelPresentation cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S
  obtain ⟨pST⟩ := exists_modelPresentation cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB (S ⊔ T)
  obtain ⟨cofS, fibS, hi⟩ := pS.exists_iterated_certificate cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB pST
  exact ⟨pS, pST, cofS, fibS, hi⟩

end SerrePositivity.Bousfield
