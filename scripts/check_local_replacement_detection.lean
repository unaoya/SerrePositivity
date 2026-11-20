import SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalEquivalences
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorLiftingClass
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ArrowLiftingClass
import SerrePositivity.HomotopicalAlgebra.Localization.LocalBoundaryCharacterization
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Bousfield SerrePositivity.HomotopyFunctionComplex

-- Arbitrary right class, with no model structure on C or Arrow C.
example {D : Type u} [Category.{v} D] [HasPushouts D] [HasTerminal D]
    (Q : MorphismProperty D) [Q.ContainsIdentities] {F G : Arrow D} (i : F ⟶ G) :
    (ArrowLiftingClass.objectwise Q).llp i ↔
      Q.llp i.left ∧ Q.llp (ArrowLiftingClass.relativeMap i) :=
  ArrowLiftingClass.mem_iff Q i

-- No model structure on the tensor category, and no cofibrancy of an arbitrary arrow.
example {D : Type u} [Category.{v} D] [HasFiniteColimits D]
    (A : SimplexCategory ⥤ D) (Q : MorphismProperty D)
    (h : ∀ n : ℕ, Q.llp (FiniteTensor.map A (SSet.boundary.{v} n).ι))
    {X Y : SSet.{v}} [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Y.Finite]
    (i : X ⟶ Y) [Mono i] : Q.llp (FiniteTensor.map A i) :=
  FiniteTensor.LiftingClass.map_mono_mem A Q h i

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (f : Arrow C) (Y : C) [IsFibrant Y] :
    fibrations SSet.{v} (ArrowFrames.testMap cof f Y) :=
  ArrowFrames.testMap_fibration cof hfib f Y

example (S : MorphismProperty C) (Y : C) [IsFibrant Y] :
    localObjects cof fib S Y ↔
      (LocalBoundaryGenerators.generators cof S).rlp (terminal.from Y) :=
  LocalBoundaryGenerators.localObjects_iff_rlp cof fib hcof hfib S Y

example (I J : MorphismProperty C)
    [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (S : MorphismProperty C) (Y : C) :
    localFibrantObjects cof fib S Y ↔
      (LocalFibrantApproximation.generators J cof S).rlp (terminal.from Y) :=
  LocalBoundaryGenerators.localFibrantObjects_iff_rlp cof fib hcof hfib I J S Y

example (S : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
    (hX : localObjects cof fib S X) (hY : localObjects cof fib S Y) :
    localEquivalences cof fib S f ↔ weakEquivalences C f :=
  localEquivalence_iff_weakEquivalence_between_localObjects cof fib hcof hfib S f hX hY

-- The local-unit condition is deliberately an explicit input; locality of R(X) alone is insufficient.
example [IsLocallyPresentable.{w} C] (I J : MorphismProperty C)
    [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (S : MorphismProperty C) (R : C ⥤ C) [R.IsAccessible.{w}] (η : 𝟭 C ⟶ R)
    (hR : ∀ X, localObjects cof fib S (R.obj X))
    (hη : ∀ X, localEquivalences cof fib S (η.app X)) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory
        (SerrePositivity.Smith.arrowProperty (localEquivalences cof fib S)).FullSubcategory κ ∧
      (SerrePositivity.Smith.arrowInclusion (localEquivalences cof fib S)).IsCardinalAccessible κ :=
  exists_accessible_localEquivalences_of_localUnit I J cof fib hcof hfib S R η hR hη

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.LocalReplacementDetection,
    `SerrePositivity.HomotopicalAlgebra.Localization.AccessibleLocalEquivalences,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorLiftingClass,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ArrowLiftingClass,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ArrowTensor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeSubcomplexTensor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLiftingConverse,
    `SerrePositivity.HomotopicalAlgebra.Localization.ArrowFrameFibrations,
    `SerrePositivity.HomotopicalAlgebra.Localization.LocalBoundaryCharacterization]
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
  logInfo m!"Local replacement detection audit passed: {count} declarations in {seen.size} modules."
