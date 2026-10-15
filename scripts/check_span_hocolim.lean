import SerrePositivity.HomotopicalAlgebra.Diagram.SpanHomotopyColimit
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
    [SerrePositivity.ModelGeneration.CofibrantlyGenerated.{w} I J]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    (K : Type w) [SmallCategory K] (e : K ≌ WalkingSpan) (D : K ⥤ C)
    (hD : cofibrations C (D.map (e.inverse.map WalkingSpan.Hom.fst))) :
    weakEquivalences C ((HomotopyColimit.comparison K I J).app D) :=
  HomotopyColimit.comparison_weakEquivalence_of_span K e I J D hD

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveReindexing,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SpanCofibrations,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveSpan,
    `SerrePositivity.HomotopicalAlgebra.Diagram.PushoutComparison,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SpanHomotopyColimit]
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
