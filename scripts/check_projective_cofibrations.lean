import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveCofibrations
import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- Only the forward implication is asserted. No objectwise
-- characterization of projective cofibrations is assumed.
example {F G : K ⥤ C} (f : F ⟶ G)
    (hf : let := Projective.modelCategory K I J; Cofibration f) (k : K) :
    Cofibration (f.app k) := Projective.cofibration_app K I J f hf k

example (F : K ⥤ C)
    (hF : let := Projective.modelCategory K I J; IsCofibrant F) (k : K) :
    IsCofibrant (F.obj k) := Projective.isCofibrant_obj K I J F hF k

-- The specified replacement used by the actual hocolim is pointwise
-- cofibrant without an input cofibrancy assumption on F.
example (F : K ⥤ C) (k : K) :
    IsCofibrant (((HomotopyColimit.replacement K I J).obj F).obj k) :=
  Projective.isCofibrant_obj K I J _ (HomotopyColimit.replacement_isCofibrant K I J F) k

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveCofibrations]
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
  logInfo m!"Projective cofibration evaluation audit passed: {count} declarations in {seen.size} modules."
