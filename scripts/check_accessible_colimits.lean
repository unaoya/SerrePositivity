import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u v' u' s t
noncomputable section
open CategoryTheory CategoryTheory.Limits SerrePositivity.Smith.AccessibleColimits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

-- The fixed cardinal is retained. No accessibility of C or D is assumed here.
example {K : Type t} [Category.{s} K] [HasColimitsOfShape K C]
    (F : K ⥤ D ⥤ C) [∀ k, (F.obj k).IsCardinalAccessible κ] :
    (colimit F).IsCardinalAccessible κ := colimit_isCardinalAccessible F κ

-- A cell-attachment pushout will be treated as a colimit of accessible vertices.
example [HasPushouts C] (F : WalkingSpan ⥤ D ⥤ C)
    [∀ k, (F.obj k).IsCardinalAccessible κ] :
    (pointwiseColimit F).IsCardinalAccessible κ := pointwiseColimit_isCardinalAccessible F κ

-- The transfinite index need not lie in the accessibility cardinal's universe.
example (o : Ordinal.{t}) [HasColimitsOfShape o.ToType C]
    (F : o.ToType ⥤ D ⥤ C) [∀ j, (F.obj j).IsCardinalAccessible κ] :
    (colimit F).IsCardinalAccessible κ := colimit_isCardinalAccessible F κ

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleColimits do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No accessible colimit declarations audited"
  logInfo m!"Accessible colimit audit passed: {count} declarations, standard axioms only."
