import SerrePositivity.HomotopicalAlgebra.Localization.ChoiceIndependence
import SerrePositivity.HomotopicalAlgebra.Localization.Representatives
import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFactorization
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Bousfield

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof cof' : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fib fib' : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (S : MorphismProperty C)

-- These closure laws are inferred for the actual class, rather than postulated.
example : (localEquivalences cof fib S).HasTwoOutOfThreeProperty := inferInstance
example : (localEquivalences cof fib S).IsStableUnderRetracts := inferInstance
example : (localEquivalences cof fib S).ContainsIdentities := inferInstance

example : weakEquivalences C ≤ localEquivalences cof fib S :=
  weakEquivalences_le_localEquivalences cof fib hcof S
example : S ≤ localEquivalences cof fib S := generators_le_localEquivalences cof fib S

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : localEquivalences cof fib S g) (hfg : localEquivalences cof fib S (f ≫ g)) :
    localEquivalences cof fib S f := (localEquivalences cof fib S).of_postcomp f g hg hfg

example {X Y Z T : C} {f : X ⟶ Y} {g : Z ⟶ T} (h : RetractArrow f g)
    (hg : localEquivalences cof fib S g) : localEquivalences cof fib S f :=
  (localEquivalences cof fib S).of_retract h hg

-- Neither the targets nor the source objects of S must be cofibrant/fibrant.
example {Y Z : C} (q : Y ⟶ Z) (hq : weakEquivalences C q) :
    localObjects cof fib S Y ↔ localObjects cof fib S Z :=
  localObjects_iff_of_weakEquivalence cof fib hcof S q hq

example {X Y : C} (f : X ⟶ Y) :
    localEquivalences cof fib S f ↔
      ∀ Z, localFibrantObjects cof fib S Z → mappingTest cof fib Z f :=
  localEquivalences_iff_fibrant cof fib hcof S f

-- Two independent resolutions and target replacements give equal predicates/classes.
example : localObjects cof fib S = localObjects cof' fib' S :=
  localObjects_choices_eq cof cof' fib fib' hcof S
example : localEquivalences cof fib S = localEquivalences cof' fib' S :=
  localEquivalences_choices_eq cof cof' fib fib' hcof S

-- Arbitrary zigzags of weak squares, beyond a single replacement functor.
example (T : MorphismProperty C) (h : SameWeakRepresentatives S T) :
    localEquivalences cof fib S = localEquivalences cof fib T :=
  localEquivalences_eq_of_weakRepresentatives cof fib hcof h

example (Y : C) (a b : Arrow C) (h : Relation.EqvGen weakArrowStep a b) :
    mappingTest cof fib Y a.hom ↔ mappingTest cof fib Y b.hom :=
  mappingTest_iff_of_weakArrowZigzag cof fib hcof Y h

-- Apply representative independence to the actual cofibrant replacement
-- restricted from the supplied model factorization.
example :
    localEquivalences cof fib (S.strictMap (Smith.AccessibleFactorization.initialRestriction cof)) =
      localEquivalences cof fib S :=
  localEquivalences_strictMap cof fib hcof S
    (Smith.AccessibleFactorization.initialRestriction cof)
    (Smith.AccessibleFactorization.initialComparison cof)
    (fun X => (Smith.AccessibleFactorization.initialComparison_mem cof X).2)

example (Y : C) : localObjects cof fib ⊥ Y := MappingTests.localObjects_bot _ _ Y

example (hS : S ≤ weakEquivalences C) (Y : C) : localObjects cof fib S Y :=
  localObjects_of_le_weakEquivalences cof fib hcof hS Y

example : localEquivalences cof fib (S ⊔ weakEquivalences C) = localEquivalences cof fib S :=
  localEquivalences_sup_weakEquivalences cof fib hcof S

example : localEquivalences cof fib (localEquivalences cof fib S) = localEquivalences cof fib S :=
  MappingTests.localEquivalences_idempotent _ _ S

-- Cofibrant generation supplies the data; no functorial-factorization assumption
-- is left to the caller. The small-object universe w is independent of u and v.
example (I J : MorphismProperty C) [ModelGeneration.CofibrantlyGenerated.{w} I J] :
    ∃ (c : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
      (r : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)),
      weakEquivalences C ≤ localEquivalences c r S := by
  have := ModelGeneration.hasFunctorialFactorization_cofibration_trivialFibration I J
  have := ModelGeneration.hasFunctorialFactorization_trivialCofibration_fibration I J
  exact ⟨MorphismProperty.functorialFactorizationData _ _,
    MorphismProperty.functorialFactorizationData _ _,
    weakEquivalences_le_localEquivalences _ _ hcof S⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.MappingTests,
    `SerrePositivity.HomotopicalAlgebra.Localization.Basic,
    `SerrePositivity.HomotopicalAlgebra.Localization.ChoiceIndependence,
    `SerrePositivity.HomotopicalAlgebra.Localization.Representatives]
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
  logInfo m!"Bousfield locality audit passed: {count} declarations in {seen.size} modules."
