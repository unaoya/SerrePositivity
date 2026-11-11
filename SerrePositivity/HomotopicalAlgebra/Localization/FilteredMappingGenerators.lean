module

public import SerrePositivity.HomotopicalAlgebra.Localization.HocolimMappingTests
public import SerrePositivity.HomotopicalAlgebra.Diagram.FilteredHomotopyColimit

/-! # Extending covariant RMap tests from a filtered generating family

At a cardinal where original weak equivalences are closed under filtered
colimits, an actual filtered generator suffices to test every source.
The theorem does not mistake ordinary density alone for homotopy density.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.DiagramModel

namespace SerrePositivity.Bousfield.HomotopyGenerators
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

include I J IS JS hcof hfib hw in
lemma tests_of_filtered_generator (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits.{w} (Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ]
    [(Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ]
    (P : ObjectProperty C) (hP : P.IsCardinalFilteredGenerator κ)
    {Y Z : C} (f : Y ⟶ Z)
    (hf : ∀ A, P A → weakEquivalences SSet.{w}
      (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op A)).map f)) (X : C) :
    weakEquivalences SSet.{w}
      (((SmallHomComparison.chosenHom cof fib).obj (Opposite.op X)).map f) := by
  obtain ⟨K, hK, hfil, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  let e : colimit p.diag ≅ X := (colimit.isColimit _).coconePointUniqueUpToIso p.isColimit
  let a : (HomotopyColimit.functor K I J).obj p.diag ⟶ X :=
    (HomotopyColimit.comparison K I J).app p.diag ≫ e.hom
  have ha : weakEquivalences C a := (weakEquivalences C).comp_mem _ _
    (HomotopyColimit.comparison_weakEquivalence_of_filtered I J κ K p.diag)
    ((weakEquivalences C).of_isIso e.hom)
  have hs := map_at_hocolim_weakEquivalence K I J IS JS cof fib hcof hfib hw p.diag f
    (fun k => hf (p.diag.obj k) (p.prop_diag_obj k))
  exact map_at_source_of_weakComparison cof fib hcof a ha f hs

include I J IS JS hcof hfib hw in
lemma exists_small_test_family :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P),
        P.IsCardinalFilteredGenerator κ ∧
          ∀ (cof' : MorphismProperty.FunctorialFactorizationData
              (cofibrations C) (trivialFibrations C))
            (fib' : MorphismProperty.FunctorialFactorizationData
              (trivialCofibrations C) (fibrations C)) {Y Z : C} (f : Y ⟶ Z),
            (∀ A, P A → weakEquivalences SSet.{w}
              (((SmallHomComparison.chosenHom cof' fib').obj (Opposite.op A)).map f)) →
            ∀ X, weakEquivalences SSet.{w}
              (((SmallHomComparison.chosenHom cof' fib').obj (Opposite.op X)).map f) := by
  obtain ⟨κ₀, h₀, hC⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₁, h₁, hW, hι⟩ := Smith.exists_accessible_weakEquivalences I J
  obtain ⟨κ, hκ, hκ₀, hκ₁⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κ₁
  have := hκ₀.isCardinalAccessibleCategory C
  have := hκ₁.isCardinalAccessibleCategory
    (Smith.arrowProperty (weakEquivalences C)).FullSubcategory
  have := Functor.isCardinalAccessible_of_le
    (Smith.arrowInclusion (weakEquivalences C)) hκ₁.le
  obtain ⟨P, hsmall, hP⟩ := HasCardinalFilteredGenerator.exists_small_generator C κ
  exact ⟨κ, hκ, P, hsmall, hP, fun cof' fib' {Y Z} f hf X =>
    tests_of_filtered_generator I J IS JS cof' fib' hcof hfib hw κ P hP f hf X⟩

end SerrePositivity.Bousfield.HomotopyGenerators
