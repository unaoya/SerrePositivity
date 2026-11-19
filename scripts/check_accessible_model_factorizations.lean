import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Smith

variable {C : Type u} [Category.{v} C]

-- The hom universe is independent of the small-object universe.
example [IsLocallyPresentable.{w} C] (I J : MorphismProperty C)
    [I.IsSmall.{w}] [J.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ (dI : MorphismProperty.FunctorialFactorizationData I.rlp.llp I.rlp)
        (dJ : MorphismProperty.FunctorialFactorizationData J.rlp.llp J.rlp),
        dI.Z.IsCardinalAccessible κ ∧ dJ.Z.IsCardinalAccessible κ :=
  exists_common_accessible_generated_factorizations I J

example [ModelCategory C] [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : AccessibleModelFactorizations C κ,
        d.Q.IsCardinalAccessible κ ∧ d.R.IsCardinalAccessible κ ∧
        (AccessibleFactorization.leftFactor d.cofibrationData).IsCardinalAccessible κ ∧
        (AccessibleFactorization.rightFactor d.cofibrationData).IsCardinalAccessible κ ∧
        (AccessibleFactorization.leftFactor d.fibrationData).IsCardinalAccessible κ ∧
        (AccessibleFactorization.rightFactor d.fibrationData).IsCardinalAccessible κ ∧
        (∀ X, IsCofibrant (d.Q.obj X)) ∧ (∀ X, IsFibrant (d.R.obj X)) ∧
        (∀ X, trivialFibrations C (d.q.app X)) ∧
        (∀ X, trivialCofibrations C (d.r.app X)) := by
  have := locallyPresentable_hasColimits (C := C)
  obtain ⟨κ, hκ, ⟨d⟩⟩ := exists_accessible_model_factorizations C I J
  exact ⟨κ, hκ, d, d.Q_isCardinalAccessible, d.R_isCardinalAccessible,
    d.cofibration_left_isCardinalAccessible, d.cofibration_right_isCardinalAccessible,
    d.fibration_left_isCardinalAccessible, d.fibration_right_isCardinalAccessible,
    d.Q_isCofibrant, d.R_isFibrant, d.q_trivialFibration, d.r_trivialCofibration⟩

example [ModelCategory C] {κ κ' : Cardinal.{w}} [Fact κ.IsRegular] [Fact κ'.IsRegular]
    (d : AccessibleModelFactorizations C κ) (h : κ ≤ κ') :
    (d.atLarger κ' h).Q.IsCardinalAccessible κ' ∧
      (d.atLarger κ' h).R.IsCardinalAccessible κ' :=
  ⟨(d.atLarger κ' h).Q_isCardinalAccessible, (d.atLarger κ' h).R_isCardinalAccessible⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleHomTransport,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleGeneratedPair,
    `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleModelFactorizations]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if modules.size != expected.size then throwError "Not all model-accessibility modules were audited"
  logInfo m!"Accessible model factorization audit passed: {count} declarations in 3 modules, standard axioms only."
