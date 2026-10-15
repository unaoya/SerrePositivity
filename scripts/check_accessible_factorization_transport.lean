import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Smith.AccessibleFactorization

variable {C : Type u} [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

example {D : Type u'} [Category.{v'} D] (F : D ⥤ Arrow C)
    [(F ⋙ Arrow.leftFunc).IsCardinalAccessible κ]
    [(F ⋙ Arrow.rightFunc).IsCardinalAccessible κ] : F.IsCardinalAccessible κ :=
  arrowFunctor_isCardinalAccessible F κ

-- The premise is explicit: this does not infer accessibility from functoriality.
example [HasColimitsOfSize.{w, w} C] {L R : MorphismProperty C}
    (d : MorphismProperty.FunctorialFactorizationData L R) [d.Z.IsCardinalAccessible κ] :
    (leftFactor d).IsCardinalAccessible κ ∧ (rightFactor d).IsCardinalAccessible κ :=
  ⟨leftFactor_isCardinalAccessible d κ, rightFactor_isCardinalAccessible d κ⟩

example [ModelCategory C] {L R : MorphismProperty C}
    (d : MorphismProperty.FunctorialFactorizationData L R) [d.Z.IsCardinalAccessible κ] :
    (initialRestriction d).IsCardinalAccessible κ ∧
      (terminalRestriction d).IsCardinalAccessible κ :=
  ⟨initialRestriction_isCardinalAccessible d κ, terminalRestriction_isCardinalAccessible d κ⟩

example [ModelCategory C]
    (d : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C)) (X : C) :
    IsCofibrant ((initialRestriction d).obj X) ∧
      trivialFibrations C ((initialComparison d).app X) :=
  ⟨initialRestriction_isCofibrant d X, initialComparison_mem d X⟩

example [ModelCategory C]
    (d : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C)) (X : C) :
    IsFibrant ((terminalRestriction d).obj X) ∧
      trivialCofibrations C ((terminalComparison d).app X) :=
  ⟨terminalRestriction_isFibrant d X, terminalComparison_mem d X⟩

-- Existing replacement choices are the corresponding restrictions of their data.
example [ModelCategory C]
    [(cofibrations C).HasFunctorialFactorization (trivialFibrations C)] :
    SerrePositivity.ModelReplacement.cofibrantReplacement C = initialRestriction
      (MorphismProperty.functorialFactorizationData (cofibrations C) (trivialFibrations C)) := rfl

example [ModelCategory C]
    [(trivialCofibrations C).HasFunctorialFactorization (fibrations C)] :
    SerrePositivity.ModelReplacement.fibrantReplacement C = terminalRestriction
      (MorphismProperty.functorialFactorizationData (trivialCofibrations C) (fibrations C)) := rfl

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleFactorization do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No accessible factorization declarations audited"
  logInfo m!"Accessible factorization transport audit passed: {count} declarations, standard axioms only."
