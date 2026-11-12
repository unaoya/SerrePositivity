module

public import SerrePositivity.HomotopicalAlgebra.Localization.ReplacementData
public import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalReplacement

/-! # A chosen accessible local replacement with its actual unit

The choice uses the constructed small-object replacement. Accessibility,
locality and the local-equivalence unit are outputs of its existence proof.
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


include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma exists_accessible_localReplacementData (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ d : LocalReplacementData.{v, u} cof fib S, d.L.IsAccessible.{w} := by
  obtain ⟨κ, hκ, R, η, hR, hX⟩ := exists_accessible_localReplacement cof fib I J IS JS
    hcof hfib hw hcofV hfibV hcofB hfibB S
  have : R.IsCardinalAccessible κ := hR
  exact ⟨@LocalReplacementData.mk C _ original simplicialV cof fib S R η
    (fun X => (hX X).1) (fun X => (hX X).2.1) (fun X => (hX X).2.2),
    Functor.isAccessible_of_isCardinalAccessible R κ⟩

/-- The specified replacement, including its cofibrant local-equivalence unit. -/
def localReplacementData (S : MorphismProperty C) [S.IsSmall.{w}] :
    LocalReplacementData.{v, u} cof fib S :=
  Classical.choose (exists_accessible_localReplacementData cof fib I J IS JS
    hcof hfib hw hcofV hfibV hcofB hfibB S)

lemma localReplacementData_isAccessible (S : MorphismProperty C) [S.IsSmall.{w}] :
    (localReplacementData cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S).L.IsAccessible.{w} :=
  Classical.choose_spec (exists_accessible_localReplacementData cof fib I J IS JS
    hcof hfib hw hcofV hfibV hcofB hfibB S)

end SerrePositivity.Bousfield
