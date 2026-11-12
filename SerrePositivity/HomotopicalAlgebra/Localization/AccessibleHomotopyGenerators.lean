module

public import SerrePositivity.HomotopicalAlgebra.Localization.HomotopyGenerators
public import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalObjects
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomAccessible

/-! # The L1 common bound and small homotopy generating family

Local objects and their inclusion, original weak equivalences and their
inclusion, specified accessible factorizations, and the actual RMap tests
on a fixed small cofibrant generating family all share one regular bound.
The detecting family works for every choice of source factorizations.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

include I J IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
lemma exists_accessible_localObjects_and_generators (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (d : Smith.AccessibleModelFactorizations C κ)
      (ι : Type w) (G : ι → C),
      IsCardinalAccessibleCategory C κ ∧
      (∀ i, IsCofibrant (G i)) ∧ (∀ i, IsCardinalPresentable (G i) κ) ∧
      (∀ i, ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
        (Opposite.op (G i))).IsCardinalAccessible κ) ∧
      (∀ f : Arrow C, S f.hom → (HomotopyFunctionComplex.MappingTests.arrow
        (SmallHomComparison.chosenHom d.cofibrationData d.fibrationData)
          f).IsCardinalAccessible κ) ∧
      IsCardinalAccessibleCategory (Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
      (Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ ∧
      IsCardinalAccessibleCategory (ObjectProperty.FullSubcategory
        (localObjects.{v,u} (C := C) cof fib S)) κ ∧
      (ObjectProperty.ι (localObjects.{v,u} (C := C) cof fib S)).IsCardinalAccessible κ ∧
      ∀ (cof' : MorphismProperty.FunctorialFactorizationData
          (cofibrations C) (trivialFibrations C))
        (fib' : MorphismProperty.FunctorialFactorizationData
          (trivialCofibrations C) (fibrations C)) {Y Z : C} (f : Y ⟶ Z),
        weakEquivalences C f ↔ ∀ i, weakEquivalences SSet.{w}
          (((SmallHomComparison.chosenHom cof' fib').obj (Opposite.op (G i))).map f) := by
  obtain ⟨κG, hκG, ι, G, hcofG, hpG, hdetect⟩ :=
    HomotopyGenerators.exists_small_presentable_cofibrant_generators
      hcofW hfibW hcofV hfibV hcofM hfibM I J IS JS hw
  let s : Sum ι S.toSet → Arrow C :=
    Sum.elim (fun i => Arrow.mk (𝟙 (G i))) (fun f => f.val)
  obtain ⟨κF, hκF, d, hW, hιW, htests, _⟩ :=
    SmallHomComparison.exists_accessible_mapping_tests I J s
  obtain ⟨κL, hκL, hPL, hιL⟩ := exists_accessible_localObjects cof fib I J
    hcofW hfibW hcofV hfibV hcofM hfibM S
  obtain ⟨κC, hκC, hC⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₀, hκ₀, hF₀, hL₀⟩ := Cardinal.SharplyLT.exists_of_pair κF κL
  obtain ⟨κ₁, hκ₁, h₀₁, hG₁⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κG
  obtain ⟨κ, hκ, h₁κ, hCκ⟩ := Cardinal.SharplyLT.exists_of_pair κ₁ κC
  have hFκ := hF₀.trans (h₀₁.trans h₁κ)
  have hLκ := hL₀.trans (h₀₁.trans h₁κ)
  have hGκ := hG₁.trans h₁κ
  refine ⟨κ, hκ, d.atLarger κ hFκ.le, ι, G, hCκ.isCardinalAccessibleCategory C, hcofG, ?_, ?_, ?_,
    hFκ.isCardinalAccessibleCategory _,
    Functor.isCardinalAccessible_of_le _ hFκ.le,
    hLκ.isCardinalAccessibleCategory _,
    Functor.isCardinalAccessible_of_le _ hLκ.le, hdetect⟩
  · intro i
    have := hpG i
    exact isCardinalPresentable_of_le _ hGκ.le
  · intro i
    change ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
      (Opposite.op (G i))).IsCardinalAccessible κ
    have : ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
      (Opposite.op (G i))).IsCardinalAccessible κF := (htests (Sum.inl i)).1
    exact Functor.isCardinalAccessible_of_le _ hFκ.le
  · intro f hf
    change (HomotopyFunctionComplex.MappingTests.arrow
      (SmallHomComparison.chosenHom d.cofibrationData d.fibrationData) f).IsCardinalAccessible κ
    have : ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
      (Opposite.op f.left)).IsCardinalAccessible κF := (htests (Sum.inr ⟨f, hf⟩)).1
    have : ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
      (Opposite.op f.right)).IsCardinalAccessible κF := (htests (Sum.inr ⟨f, hf⟩)).2
    have := HomotopyFunctionComplex.MappingTests.arrow_isCardinalAccessible
      (SmallHomComparison.chosenHom d.cofibrationData d.fibrationData) f κF
    exact Functor.isCardinalAccessible_of_le _ hFκ.le

end SerrePositivity.Bousfield
