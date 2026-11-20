import SerrePositivity.HomotopicalAlgebra.Diagram.SpanHomotopyColimit
import SerrePositivity.HomotopicalAlgebra.Localization.LeftProperPushout
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vK uK vL uL
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

-- Reindexing arbitrary lifting classes does not need any target model structure.
example {K : Type uK} [Category.{vK} K] {L : Type uL} [Category.{vL} L]
    {C : Type u} [Category.{v} C] (e : K ≌ L) (Q : MorphismProperty C)
    {F G : K ⥤ C} (a : F ⟶ G) (ha : (Q.functorCategory K).llp a) :
    (Q.functorCategory L).llp (Functor.whiskerLeft e.inverse a) :=
  ProjectiveReindexing.llp_map e Q a ha

variable {C : Type u} [Category.{v} C] [ModelCategory C]

example {P D : WalkingSpan ⥤ C} (i : P ⟶ D) (hP : IsInitial P)
    (hi : ((trivialFibrations C).functorCategory WalkingSpan).llp i) :
    cofibrations C (D.map WalkingSpan.Hom.fst) ∧
      cofibrations C (D.map WalkingSpan.Hom.snd) :=
  ⟨SpanCofibrations.fst_cofibration i hP hi, SpanCofibrations.snd_cofibration i hP hi⟩

-- Independent universes, one cofibration leg, and no cofibrancy of objects.
example [IsLocallyPresentable.{w} C] (I J : MorphismProperty C)
    [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    (K : Type w) [SmallCategory K] (e : K ≌ WalkingSpan) (D : K ⥤ C)
    (hD : cofibrations C (D.map (e.inverse.map WalkingSpan.Hom.fst))) :
    weakEquivalences C ((HomotopyColimit.comparison K I J).app D) :=
  HomotopyColimit.comparison_weakEquivalence_of_span K e I J D hD

open SerrePositivity.Bousfield
variable [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w})
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

-- Arbitrary S and arbitrary pushout; none of its four objects is assumed cofibrant.
example (S : MorphismProperty C) {A B D P : C}
    {f : A ⟶ B} {g : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    (s : IsPushout f g l r) (hf : cofibrations C f)
    (hflocal : localEquivalences.{v, u} (C := C) cof fib S f) :
    localEquivalences.{v, u} (C := C) cof fib S r :=
  localEquivalence_of_pushout cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S s hf hflocal

-- The actual stability class required by Smith recognition.
example (S : MorphismProperty C) :
    (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChange :=
  cof_localEquivalences_pushoutStable cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveReindexing,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SpanCofibrations,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveSpan,
    `SerrePositivity.HomotopicalAlgebra.Diagram.PushoutComparison,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SpanHomotopyColimit,
    `SerrePositivity.HomotopicalAlgebra.Localization.SpanLocalEquivalences,
    `SerrePositivity.HomotopicalAlgebra.Localization.LeftProperPushout]
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
  logInfo m!"Span hocolim comparison audit passed: {count} declarations in {seen.size} modules."
