module

public import SerrePositivity.HomotopicalAlgebra.Localization.FilteredMappingGenerators
public import SerrePositivity.HomotopicalAlgebra.Localization.CovariantDetection

/-! # Small cofibrant homotopy generators for a combinatorial model category

A small ordinary filtered generator at a common sufficiently large cardinal
is replaced by the degree-zero objects of actual cofibrant resolutions.
The resulting fixed small cofibrant family detects all original weak
equivalences by covariant RMap, for every choice of source factorizations.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.HomotopyGenerators
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

include hcofW hfibW hcofV hfibV hcofM hfibM in
lemma weakEquivalence_of_small_covariant_mappingTests
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {Y Z : C} (f : Y ⟶ Z)
    (hf : ∀ X, weakEquivalences SSet.{w}
      (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op X)).map f)) :
    weakEquivalences C f := by
  apply weakEquivalence_of_covariant_mappingTests cof fib hcofV hfibV f
  intro X
  exact (SimplicialModel.UniverseLift.weakEquivalences_iff_of_liftedArrowIso.{v,w}
    hcofW hfibW hcofM hfibM hcofV hfibV _ _
    (SmallHomComparison.targetArrowIso (cosimplicialResolutionFamily cof).obj
      (fibrantTarget fib) (Opposite.op X) f)).mp (hf X)

variable (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include I J IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
lemma exists_small_cofibrant_generators
    (seed : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    ∃ (ι : Type w) (G : ι → C), (∀ i, IsCofibrant (G i)) ∧
      ∀ (cof : MorphismProperty.FunctorialFactorizationData
          (cofibrations C) (trivialFibrations C))
        (fib : MorphismProperty.FunctorialFactorizationData
          (trivialCofibrations C) (fibrations C)) {Y Z : C} (f : Y ⟶ Z),
        weakEquivalences C f ↔ ∀ i, weakEquivalences SSet.{w}
          (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op (G i))).map f) := by
  obtain ⟨κ, hκ, P, hsmall, hP, htests⟩ :=
    exists_small_test_family I J IS JS hcofW hfibW hw
  obtain ⟨ι, A, hA⟩ := ObjectProperty.Small.exists_eq_ofObj P
  let G : ι → C := fun i =>
    ((cosimplicialResolutionFamily seed).obj.obj (A i)).obj (SimplexCategory.mk 0)
  refine ⟨ι, G, ?_, ?_⟩
  · intro i
    exact cosimplicialFrame_isCofibrant_obj _
      ((cosimplicialResolutionFamily seed).cofibrant (A i)) _
  · intro cof fib Y Z f
    constructor
    · intro hf i
      exact SmallHomComparison.chosenHom_map_target_weakEquivalence hcofW hfibW cof fib
        (Opposite.op (G i)) f hf
    · intro hf
      apply weakEquivalence_of_small_covariant_mappingTests
        hcofW hfibW hcofV hfibV hcofM hfibM cof fib f
      apply htests cof fib f
      intro X hX
      rw [hA, ObjectProperty.ofObj_iff] at hX
      obtain ⟨i, rfl⟩ := hX
      exact map_at_source_of_weakComparison cof fib hcofW
        (((cosimplicialResolutionFamily seed).augmentation.app (A i)).app (SimplexCategory.mk 0))
        (((cosimplicialResolutionFamily seed).atObject (A i)).augmentation_weakEquivalence _)
        f (hf i)

include I J IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
/-- Combinatoriality supplies the seed factorization. A single small
cofibrant family detects weak equivalences for all specified Q/R choices,
and its objects have an explicitly quantified common presentability bound. -/
lemma exists_small_presentable_cofibrant_generators :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (ι : Type w) (G : ι → C),
      (∀ i, IsCofibrant (G i)) ∧ (∀ i, IsCardinalPresentable (G i) κ) ∧
      ∀ (cof : MorphismProperty.FunctorialFactorizationData
          (cofibrations C) (trivialFibrations C))
        (fib : MorphismProperty.FunctorialFactorizationData
          (trivialCofibrations C) (fibrations C)) {Y Z : C} (f : Y ⟶ Z),
        weakEquivalences C f ↔ ∀ i, weakEquivalences SSet.{w}
          (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op (G i))).map f) := by
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration I J
  obtain ⟨ι, G, hcofG, hdetect⟩ := exists_small_cofibrant_generators
    hcofW hfibW hcofV hfibV hcofM hfibM I J IS JS hw
    (MorphismProperty.functorialFactorizationData (cofibrations C) (trivialFibrations C))
  obtain ⟨κ, hκ, hG⟩ := ObjectProperty.le_isCardinalPresentable (ObjectProperty.ofObj G)
  refine ⟨κ, hκ, ι, G, hcofG, ?_, hdetect⟩
  intro i
  apply hG
  rw [ObjectProperty.ofObj_iff]
  exact ⟨i, rfl⟩

end SerrePositivity.Bousfield.HomotopyGenerators
