import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleHomotopyGenerators
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Bousfield

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)

-- One fixed small cofibrant family tests the same class for two arbitrary Q/R choices.
example
    (cof₁ cof₂ : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    ∃ (ι : Type w) (G : ι → C), (∀ i, IsCofibrant (G i)) ∧
      ∀ {Y Z : C} (f : Y ⟶ Z),
        (∀ i, weakEquivalences SSet.{w}
          (((SmallHomComparison.chosenHom cof₁ fib₁).obj (Opposite.op (G i))).map f)) ↔
        ∀ i, weakEquivalences SSet.{w}
          (((SmallHomComparison.chosenHom cof₂ fib₂).obj (Opposite.op (G i))).map f) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated.{w} hcofW hfibW
  obtain ⟨κ, hκ, ι, G, hG, _, hd⟩ := HomotopyGenerators.exists_small_presentable_cofibrant_generators (C := C)
    hcofW hfibW hcofV hfibV hcofM hfibM I J
    SSet.modelCategoryQuillen.I.{w} SSet.modelCategoryQuillen.J.{w} hw
  exact ⟨ι, G, hG, fun {Y Z} f => (hd cof₁ fib₁ f).symm.trans (hd cof₂ fib₂ f)⟩

-- Common bound: original local objects/inclusion, accessible chosen tests, and detection.
-- The original supplied cof/fib have no accessibility assumption.
example
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (d : SerrePositivity.Smith.AccessibleModelFactorizations C κ)
      (ι : Type w) (G : ι → C),
      IsCardinalAccessibleCategory C κ ∧
      IsCardinalAccessibleCategory (ObjectProperty.FullSubcategory (localObjects.{v,u} (C := C) cof fib S)) κ ∧
      (ObjectProperty.ι (localObjects.{v,u} (C := C) cof fib S)).IsCardinalAccessible κ ∧
      (∀ i, IsCofibrant (G i) ∧ IsCardinalPresentable (G i) κ ∧
        ((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj
          (Opposite.op (G i))).IsCardinalAccessible κ) ∧
      (∀ f : Arrow C, S f.hom → (SerrePositivity.HomotopyFunctionComplex.MappingTests.arrow
        (SmallHomComparison.chosenHom d.cofibrationData d.fibrationData) f).IsCardinalAccessible κ) ∧
      ∀ {Y Z : C} (f : Y ⟶ Z), weakEquivalences C f ↔ ∀ i, weakEquivalences SSet.{w}
        (((SmallHomComparison.chosenHom d.cofibrationData d.fibrationData).obj (Opposite.op (G i))).map f) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated.{w} hcofW hfibW
  obtain ⟨κ, hκ, d, ι, G, hC, hG, hpG, htest, hStests, _, _, hL, hιL, hd⟩ :=
    exists_accessible_localObjects_and_generators (C := C) I J SSet.modelCategoryQuillen.I.{w}
      SSet.modelCategoryQuillen.J.{w} hcofW hfibW hcofV hfibV hcofM hfibM hw cof fib S
  exact ⟨κ, hκ, d, ι, G, hC, hL, hιL,
    fun i => ⟨hG i, hpG i, htest i⟩, hStests, fun {Y Z} f => hd d.cofibrationData d.fibrationData f⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomFrameInvariance,
    `SerrePositivity.HomotopicalAlgebra.Localization.HocolimMappingTests,
    `SerrePositivity.HomotopicalAlgebra.Localization.FilteredMappingGenerators,
    `SerrePositivity.HomotopicalAlgebra.Localization.CovariantDetection,
    `SerrePositivity.HomotopicalAlgebra.Localization.HomotopyGenerators,
    `SerrePositivity.HomotopicalAlgebra.Localization.AccessibleHomotopyGenerators]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Homotopy generators audit passed: {count} declarations in {seen.size} modules."
