import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AccessibleResolutions
import Lean.Util.CollectAxioms

noncomputable section
universe w t v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

-- These are the actual previously constructed source-variable resolution
-- functors. Their accessibility is concluded from the source data.
example
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    [cof.Z.IsAccessible.{w}] : (SerrePositivity.Reedy.cosimplicialResolutionFamily cof).obj.IsAccessible.{w} :=
  cosimplicialResolutionFamily_isAccessible cof

example
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    [fib.Z.IsAccessible.{w}] : (SerrePositivity.Reedy.simplicialResolutionFamily fib).obj.IsAccessible.{w} :=
  simplicialResolutionFamily_isAccessible fib

variable (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- The full F3 input: no accessible source resolution or mapping functor
-- is assumed, and the input arrows have arbitrary endpoints.
example {ι : Type t} [Small.{w} ι] (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : SerrePositivity.Smith.AccessibleModelFactorizations C κ,
        Functor.IsCardinalAccessible
          (SerrePositivity.Reedy.cosimplicialResolutionFamily d.cofibrationData).obj κ ∧
        Functor.IsCardinalAccessible
          (SerrePositivity.Reedy.simplicialResolutionFamily d.fibrationData).obj κ ∧
        IsCardinalAccessibleCategory
          (SerrePositivity.Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (SerrePositivity.Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ ∧
        (∀ i, ((AccessibleModelMapping.hom d).obj (op (s i).left)).IsCardinalAccessible κ ∧
          ((AccessibleModelMapping.hom d).obj (op (s i).right)).IsCardinalAccessible κ) ∧
        (MappingTests.family (AccessibleModelMapping.hom d) s).IsCardinalAccessible κ :=
  exists_accessible_resolutions_and_mapping_tests I J s

-- The same output data provide actual Q/R with their existing model
-- comparisons, and both replacements are accessible at that same cardinal.
example {ι : Type t} [Small.{w} ι] (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : SerrePositivity.Smith.AccessibleModelFactorizations C κ,
        d.Q.IsCardinalAccessible κ ∧ d.R.IsCardinalAccessible κ ∧
        (∀ X, IsCofibrant (d.Q.obj X) ∧ IsFibrant (d.R.obj X)) ∧
        (∀ X, trivialFibrations C (d.q.app X) ∧ trivialCofibrations C (d.r.app X)) ∧
        (MappingTests.family (AccessibleModelMapping.hom d) s).IsCardinalAccessible κ := by
  obtain ⟨κ, hκ, d, _, _, _, _, _, ht⟩ := exists_accessible_resolutions_and_mapping_tests I J s
  exact ⟨κ, hκ, d, d.Q_isCardinalAccessible, d.R_isCardinalAccessible,
    fun X ↦ ⟨d.Q_isCofibrant X, d.R_isFibrant X⟩,
    fun X ↦ ⟨d.q_trivialFibration X, d.r_trivialCofibration X⟩, ht⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFamilies,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessiblePushoutPullback,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleRelativeBoundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleFactorization,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.AccessibleResolution,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AccessibleResolutions]
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
  logInfo m!"Accessible resolutions audit passed: {count} declarations in {seen.size} modules."
