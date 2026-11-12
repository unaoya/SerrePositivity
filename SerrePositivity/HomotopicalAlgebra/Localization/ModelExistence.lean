module

public import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalReplacement
public import SerrePositivity.HomotopicalAlgebra.Localization.Conditional
public import SerrePositivity.HomotopicalAlgebra.Localization.LocalLeftProper
public import SerrePositivity.HomotopicalAlgebra.Smith.Existence

/-! # An actual left Bousfield model from the proved Smith hypotheses

The original model is held fixed in the mapping-space definitions. The
constructed model is a separate value, accompanied by exact class equalities
and an actual small generating trivial-cofibration class.
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



structure ModelPresentation (S : MorphismProperty C) where
  model : ModelCategory C
  cofibrations_eq : model.categoryWithCofibrations.cofibrations =
    original.categoryWithCofibrations.cofibrations
  weakEquivalences_eq : model.categoryWithWeakEquivalences.weakEquivalences =
    @localEquivalences C _ original simplicialV cof fib S
  fibrations_eq : model.categoryWithFibrations.fibrations =
    (original.categoryWithCofibrations.cofibrations ⊓
      @localEquivalences C _ original simplicialV cof fib S).rlp
  generators : MorphismProperty C
  generators_small : generators.IsSmall.{w}
  generated : let := model; _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I generators

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma exists_modelPresentation (S : MorphismProperty C) [S.IsSmall.{w}] :
    Nonempty (ModelPresentation.{w} cof fib I S) := by
  let W := localEquivalences.{v, u} (C := C) cof fib S
  have : I.IsSmall.{w} := ModelGeneration.EvaluationFamily.isSmall_of_smallObjectArgument I
  obtain ⟨κ, hκ, hW, hι⟩ := exists_accessible_localEquivalences cof fib I J IS JS
    hcof hfib hw hcofV hfibV hcofB hfibB S
  have : IsAccessibleCategory.{w} (Smith.arrowProperty W).FullSubcategory := ⟨κ, hκ, hW⟩
  have : (Smith.arrowInclusion W).IsAccessible.{w} :=
    Functor.isAccessible_of_isCardinalAccessible _ κ
  have hc := localEquivalences_smithClosure cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S
  have := hc.1
  have := hc.2
  have hC : original.categoryWithCofibrations.cofibrations = I.rlp.llp :=
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J
  have hIW : I.rlp ≤ W := by
    intro A B f hf
    have ht : trivialFibrations C f :=
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I (I := I) (J := J)).le f hf
    exact weakEquivalences_le_localEquivalences cof fib hcofV S f ht.2
  let G := Smith.smithGenerators I W hIW
  have hG : G.IsSmall.{w} := inferInstance
  let : CategoryWithCofibrations C := ⟨original.categoryWithCofibrations.cofibrations⟩
  let : CategoryWithWeakEquivalences C := ⟨W⟩
  let : CategoryWithFibrations C := ⟨(I.rlp.llp ⊓ W).rlp⟩
  let m := Smith.modelCategoryOfSmith I W hC rfl rfl hIW
  have hgen : let := m; _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I G := by
    let := m
    exact Smith.cofibrantlyGeneratedOfSmith I W rfl rfl hIW
  refine ⟨@ModelPresentation.mk.{w, v, u} _ _ original cof fib I simplicialV S m
    rfl rfl ?_ G hG hgen⟩
  change (I.rlp.llp ⊓ W).rlp = (original.categoryWithCofibrations.cofibrations ⊓ W).rlp
  exact congrArg (fun P => (P ⊓ W).rlp) hC.symm

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma ModelPresentation.localFibrant_of_fibrant {S : MorphismProperty C}
    (p : ModelPresentation.{w} cof fib I S) (Y : C)
    (hY : p.model.categoryWithFibrations.fibrations (terminal.from Y)) :
    localFibrantObjects.{v, u} (C := C) cof fib S Y := by
  have hK := localFibrantGenerators_le_cof_local cof fib I J IS JS
    hcof hfib hw hcofV hfibV hcofB hfibB S
  apply LocalFibrantApproximation.localFibrant_of_rlp I J cof S fib hcofV Y
  exact MorphismProperty.antitone_rlp hK _ (p.fibrations_eq.le _ hY)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma ModelPresentation.isLocalizationModel {S : MorphismProperty C}
    (p : ModelPresentation.{w} cof fib I S) :
    IsLocalizationModel.{v, u} cof fib S p.model := by
  refine @IsLocalizationModel.mk C _ original simplicialV cof fib S p.model
    p.cofibrations_eq p.weakEquivalences_eq (fun Y => ?_)
  have forward := p.localFibrant_of_fibrant cof fib I J IS JS
    hcof hfib hw hcofV hfibV hcofB hfibB
  refine ⟨forward Y, fun hY => ?_⟩
  let d : MorphismProperty.MapFactorizationData
      (p.model.categoryWithCofibrations.cofibrations ⊓
        p.model.categoryWithWeakEquivalences.weakEquivalences)
      p.model.categoryWithFibrations.fibrations (terminal.from Y) := by
    let := p.model
    exact MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
      (terminal.from Y)
  have hZ : localFibrantObjects.{v, u} (C := C) cof fib S d.Z := by
    apply forward d.Z
    simpa only [terminal.hom_ext d.p (terminal.from d.Z)] using d.hp
  have hi : original.categoryWithCofibrations.cofibrations d.i ∧
      (@localEquivalences C _ original simplicialV cof fib S) d.i := by
    exact ⟨p.cofibrations_eq.le _ d.hi.1, p.weakEquivalences_eq.le _ d.hi.2⟩
  let := original
  have hiW : weakEquivalences C d.i :=
    (localEquivalence_iff_weakEquivalence_between_localObjects cof fib hcofV hfibV
      S d.i hY.2 hZ.2).mp hi.2
  have : Cofibration d.i := ⟨hi.1⟩
  have : WeakEquivalence d.i := ⟨hiW⟩
  have : IsFibrant Y := hY.1
  have sq : CommSq (𝟙 Y) d.i (terminal.from Y) (terminal.from d.Z) :=
    ⟨terminal.hom_ext _ _⟩
  have retract : RetractArrow (terminal.from Y) (terminal.from d.Z) :=
    { i := Arrow.homMk d.i (𝟙 _)
      r := Arrow.homMk sq.lift (𝟙 _) }
  have : p.model.categoryWithFibrations.fibrations.IsStableUnderRetracts := p.model.cm3b
  exact MorphismProperty.of_retract retract (by
    simpa only [terminal.hom_ext d.p (terminal.from d.Z)] using d.hp)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma ModelPresentation.leftProper {S : MorphismProperty C}
    (p : ModelPresentation.{w} cof fib I S) :
    p.model.categoryWithWeakEquivalences.weakEquivalences.IsStableUnderCobaseChangeAgainst
      p.model.categoryWithCofibrations.cofibrations := by
  rw [p.cofibrations_eq, p.weakEquivalences_eq]
  exact localEquivalences_leftProper cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S

omit [ModelCategory SSet.{w}] [ModelCategory SSet.{max v w}]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)] in
lemma ModelPresentation.exists_accessible_factorizations {S : MorphismProperty C}
    (p : ModelPresentation.{w} cof fib I S) :
    let := p.model
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      Nonempty (Smith.AccessibleModelFactorizations C κ) := by
  have hgen := p.generated
  let G := p.generators
  let := p.model
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I G := hgen
  exact Smith.exists_accessible_model_factorizations C I G

/-- A chosen actual model presentation, rather than an assumed localization certificate. -/
def modelPresentation (S : MorphismProperty C) [S.IsSmall.{w}] :
    ModelPresentation.{w} cof fib I S :=
  Classical.choice (exists_modelPresentation cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S)

end SerrePositivity.Bousfield
