import SerrePositivity.HomotopicalAlgebra.Localization.HocolimLocalEquivalences
import SerrePositivity.HomotopicalAlgebra.Localization.FilteredLocalEquivalences
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Bousfield SerrePositivity.DiagramModel

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w})
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)

local instance : HasColimitsOfSize.{w, w} C :=
  SerrePositivity.Smith.locallyPresentable_hasColimits (C := C)

-- Arbitrary diagrams, with no objectwise or projective cofibrancy requirement.
example (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E)
    (ha : ∀ k, smallLocalEquivalences.{w, v, u} cof fib S (a.app k)) :
    smallLocalEquivalences.{w, v, u} cof fib S ((HomotopyColimit.functor K I J).map a) :=
  HocolimSourceTests.smallLocalEquivalence_hocolim K I J IS JS cof fib hcof hfib hw S a ha

variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

-- A single bound, independent of S and all the diagrams; accessibility of W_S is not assumed.
example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular], κ ≤ μ →
      ∀ (K' : Type w) [SmallCategory K'] [IsCardinalFiltered K' μ]
        (S : MorphismProperty C) {D E : K' ⥤ C} (a : D ⟶ E),
        (∀ k, localEquivalences.{v, u} cof fib S (a.app k)) →
        localEquivalences.{v, u} cof fib S ((colim : (K' ⥤ C) ⥤ C).map a) :=
  exists_filtered_localEquivalence_colim I J IS JS cof fib hcof hfib hw
    hcofV hfibV hcofB hfibB

-- Original W_S, in independent object/Hom/presentability universes.
example (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E)
    (ha : ∀ k, localEquivalences.{v, u} cof fib S (a.app k)) :
    localEquivalences.{v, u} cof fib S ((HomotopyColimit.functor K I J).map a) :=
  HocolimSourceTests.localEquivalence_hocolim K I J IS JS cof fib hcof hfib hw
    hcofV hfibV hcofB hfibB S a ha

-- Ordinary colimit requires actual weak comparisons, rather than objectwise cofibrancy alone.
example (S : MorphismProperty C) {D E : K ⥤ C} (a : D ⟶ E)
    (ha : ∀ k, localEquivalences.{v, u} cof fib S (a.app k))
    (hD : weakEquivalences C ((HomotopyColimit.comparison K I J).app D))
    (hE : weakEquivalences C ((HomotopyColimit.comparison K I J).app E)) :
    localEquivalences.{v, u} cof fib S ((colim : (K ⥤ C) ⥤ C).map a) :=
  HocolimSourceTests.localEquivalence_colim_of_weakComparisons K I J IS JS cof fib hcof hfib hw
    hcofV hfibV hcofB hfibB S a ha hD hE

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.HocolimLocalEquivalences,
    `SerrePositivity.HomotopicalAlgebra.Localization.FilteredLocalEquivalences]
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
  logInfo m!"Hocolim local-equivalence audit passed: {count} declarations in {seen.size} modules."
