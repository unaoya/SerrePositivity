import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Smith SerrePositivity.Smith.AccessibleSmallObject

variable {C : Type u} [Category.{w} C]

-- No accessibility of the cell attachment or its iteration is assumed.
example [HasColimitsOfSize.{w, w} C] (I : MorphismProperty C)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    [I.IsCardinalForSmallObjectArgument μ]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ i : I.toSet, IsCardinalPresentable i.val.left κ]
    [∀ i : I.toSet, IsCardinalPresentable i.val.right κ] :
    (SmallObject.functorialFactorizationData I μ).Z.IsCardinalAccessible κ ∧
    (AccessibleFactorization.leftFactor
      (SmallObject.functorialFactorizationData I μ)).IsCardinalAccessible κ ∧
    (AccessibleFactorization.rightFactor
      (SmallObject.functorialFactorizationData I μ)).IsCardinalAccessible κ :=
  ⟨factorization_isCardinalAccessible I μ κ,
    leftFactor_isCardinalAccessible I μ κ, rightFactor_isCardinalAccessible I μ κ⟩

-- Local presentability and small generators suffice for the full construction.
example [IsLocallyPresentable.{w} C] (I : MorphismProperty C) [I.IsSmall.{w}] :
    letI := locallyPresentable_hasColimits (C := C)
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp,
        d.Z.IsCardinalAccessible κ ∧
        (AccessibleFactorization.leftFactor d).IsCardinalAccessible κ ∧
        (AccessibleFactorization.rightFactor d).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := C)
  exact exists_accessible_factorization I

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleSmallObject do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Small-object accessibility module was not audited"
  logInfo m!"Accessible small-object audit passed: {count} declarations, standard axioms only."
