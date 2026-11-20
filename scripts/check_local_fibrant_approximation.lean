import SerrePositivity.HomotopicalAlgebra.Localization.LocalFibrantApproximation
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Bousfield

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

-- Arbitrary original arrows, without assuming either end or the arrow itself cofibrant.
example (f : Arrow C) : SerrePositivity.Reedy.reedyLeft SerrePositivity.Reedy.simplex
    (cofibrations C) ((ArrowFrames.inclusion cof).app f) :=
  ArrowFrames.inclusion_reedyCofibration cof f

example (f : Arrow C) (n : SimplexCategory) :
    weakEquivalences C (ArrowFrames.degreeArrowComparison cof f n).left ∧
      weakEquivalences C (ArrowFrames.degreeArrowComparison cof f n).right :=
  ⟨ArrowFrames.sourceAugmentation_weakEquivalence cof f n,
    ArrowFrames.targetAugmentation_weakEquivalence cof f n⟩

variable [ModelCategory SSet.{v}]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

example (S : MorphismProperty C) (Y : C) [IsFibrant Y] :
    localObjects cof fib S Y ↔
      ∀ f : Arrow C, S f.hom → weakEquivalences SSet.{v} (ArrowFrames.testMap cof f Y) :=
  ArrowFrames.localObjects_iff_of_fibrant cof fib hcof S Y

-- Small-object and Hom universes remain independent; no SSet(w) model or enrichment is needed.
example [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (R : C ⥤ C) (η : 𝟭 C ⟶ R),
      R.IsCardinalAccessible κ ∧
      (∀ X, cofibrations C (η.app X)) ∧
      ∀ X, IsFibrant (R.obj X) ∧ localObjects cof fib S (R.obj X) := by
  obtain ⟨κ, hκ, d, _, hR, hη, hlocal⟩ :=
    LocalFibrantApproximation.exists_accessible_approximation I J cof S fib hcof
  exact ⟨κ, hκ, SerrePositivity.Smith.AccessibleFactorization.terminalRestriction d,
    SerrePositivity.Smith.AccessibleFactorization.terminalComparison d, hR, hη, hlocal⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.ArrowFrames,
    `SerrePositivity.HomotopicalAlgebra.Localization.ArrowFrameTests,
    `SerrePositivity.HomotopicalAlgebra.Localization.LocalBoundaryGenerators,
    `SerrePositivity.HomotopicalAlgebra.Localization.LocalFibrantApproximation]
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
  logInfo m!"Local fibrant approximation audit passed: {count} declarations in {seen.size} modules."
