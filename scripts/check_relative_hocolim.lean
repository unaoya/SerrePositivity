import SerrePositivity.HomotopicalAlgebra.Diagram.RelativeHomotopyColimit
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

section Categorical
variable {K : Type w} [PartialOrder K] [OrderBot K] {C : Type u} [Category.{v} C]

-- No model, continuity, or presentability assumptions in the bottom replacement itself.
example {X : C} {U V : K ⥤ C} (a : (Functor.const K).obj X ⟶ U)
    (c : (Functor.const K).obj X ⟶ V) (p : U ⟶ V) (h : a ≫ p = c) :
    BottomReplacement.comparison a ≫ p =
      BottomReplacement.change a c p h ≫ BottomReplacement.comparison c :=
  BottomReplacement.comparison_change a c p h

example {D V : K ⥤ C} (b : D ⟶ V) :
    BottomReplacement.factor b ≫ BottomReplacement.comparison (BottomReplacement.based b) = b :=
  BottomReplacement.factor_comparison b
end Categorical

section Model
variable {K : Type w} [PartialOrder K] [OrderBot K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- Arbitrary projectively cofibrant diagram: no continuity and no well-order assumption.
example (R : K ⥤ C) (hR : let := Projective.modelCategory K I J; IsCofibrant R) :
    let := Projective.modelCategory K I J;
    cofibrations (K ⥤ C) (ContinuousLifts.fromBottom R) :=
  Projective.fromBottom_cofibration_of_isCofibrant I J R hR

variable [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

example : let := Projective.modelCategory K I J;
    (weakEquivalences (K ⥤ C)).IsStableUnderCobaseChangeAgainst (cofibrations (K ⥤ C)) :=
  Projective.leftProper K I J

example (D : K ⥤ C) (hD : let := Projective.modelCategory K I J;
    cofibrations (K ⥤ C) (ContinuousLifts.fromBottom D)) :
    weakEquivalences C ((HomotopyColimit.comparison K I J).app D) :=
  HomotopyColimit.comparison_weakEquivalence_of_fromBottom I J D hD

example (X : C) :
    weakEquivalences C ((HomotopyColimit.comparison K I J).app ((Functor.const K).obj X)) :=
  HomotopyColimit.comparison_weakEquivalence_const I J X
end Model

-- Arbitrary well-ordered continuous cofibration sequence; the initial object need not be cofibrant.
example {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
    {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hstep : ∀ k, ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    weakEquivalences C ((HomotopyColimit.comparison K I J).app D) :=
  HomotopyColimit.comparison_weakEquivalence_of_continuous_leftProper I J D hstep

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.BottomReplacement,
    `SerrePositivity.HomotopicalAlgebra.Diagram.BottomReplacementMaps,
    `SerrePositivity.HomotopicalAlgebra.Diagram.BottomReplacementFactor,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveBottomCofibrancy,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveLeftProper,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ColimitFromBottom,
    `SerrePositivity.HomotopicalAlgebra.Diagram.RelativeHomotopyColimit,
    `SerrePositivity.HomotopicalAlgebra.Under.Quillen]
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
  logInfo m!"Relative hocolim audit passed: {count} declarations in {seen.size} modules."
