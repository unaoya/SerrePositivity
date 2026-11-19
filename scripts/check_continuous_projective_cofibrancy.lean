import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousHomotopyColimit
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

variable {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
  {C : Type u} [Category.{v} C]

-- Arbitrary well-ordered index and arbitrary target category: no model or initial objects needed.
example {D U V : K ⥤ C} [D.IsWellOrderContinuous] (p : U ⟶ V) (b : D ⟶ V)
    (hstep : ∀ k, ¬IsMax k →
      HasLiftingProperty (D.map (homOfLE (Order.le_succ k))) (p.app (Order.succ k)))
    (x₀ : ContinuousLifts.Partial p b ⊥) :
    ∃ l : D ⟶ U, l ≫ p = b ∧ l.app ⊥ = x₀.hom ⊥ le_rfl :=
  ContinuousLifts.exists_lift_with_base p b hstep x₀

-- Relative cofibrancy does not assume the initial stage is cofibrant, or even an initial object in C.
example (D : K ⥤ C) [D.IsWellOrderContinuous] (Q : MorphismProperty C)
    (hstep : ∀ k, ¬IsMax k → Q.llp (D.map (homOfLE (Order.le_succ k)))) :
    (Q.functorCategory K).llp (ContinuousLifts.fromBottom D) :=
  ContinuousLifts.fromBottom_llp D Q hstep

example [HasInitial C] (D : K ⥤ C) [D.IsWellOrderContinuous] (Q : MorphismProperty C)
    (hbot : Q.llp (initial.to (D.obj ⊥)))
    (hstep : ∀ k, ¬IsMax k → Q.llp (D.map (homOfLE (Order.le_succ k)))) :
    (Q.functorCategory K).llp (initial.to D) :=
  ContinuousLifts.projective_llp Q hbot hstep

variable [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- Actual projective model and actual hocolim, independent object/Hom/presentability universes.
example (D : K ⥤ C) [D.IsWellOrderContinuous] (hbot : IsCofibrant (D.obj ⊥))
    (hstep : ∀ k, ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    let := Projective.modelCategory K I J; IsCofibrant D :=
  Projective.isCofibrant_of_continuous I J D hbot hstep

example (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hstep : ∀ k, ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    let := Projective.modelCategory K I J;
    cofibrations (K ⥤ C) (ContinuousLifts.fromBottom D) :=
  Projective.fromBottom_cofibration I J D hstep

example (D : K ⥤ C) [D.IsWellOrderContinuous] (hbot : IsCofibrant (D.obj ⊥))
    (hstep : ∀ k, ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    weakEquivalences C ((HomotopyColimit.comparison K I J).app D) :=
  HomotopyColimit.comparison_weakEquivalence_of_continuous I J D hbot hstep

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftSystem,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftSuccessor,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftLimit,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousLiftInduction,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousProjectiveCofibrancy,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousRelativeCofibrancy,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousHomotopyColimit]
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
  logInfo m!"Continuous projective cofibrancy audit passed: {count} declarations in {seen.size} modules."
