import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Smith SerrePositivity.Smith.AccessibleSquares

variable {C : Type u} [Category.{w} C] {ι : Type w}

example [HasCoproducts.{w} C] (A : ι → C) :
    DependentCopower.realization A ⊣ DependentCopower.homFamily A :=
  DependentCopower.adjunction A

example [HasCoproducts.{w} C] (A : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (DependentCopower.realization A).IsCardinalAccessible κ :=
  DependentCopower.realization_isCardinalAccessible A κ

example (a : ι → Arrow C) (f : Arrow C) :
    DependentCopower.index ((squareFamily a).obj f) ≃
      SmallObject.FunctorObjIndex (fun i ↦ (a i).hom) f.hom := indexEquiv a f

-- This consumer derives a common cardinal and actual square-indexed coproduct
-- accessibility from local presentability, without assuming their accessibility.
example [IsLocallyPresentable.{w} C] (a : ι → Arrow C) :
    letI := locallyPresentable_hasColimits (C := C)
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      (squareFamily a).IsCardinalAccessible κ ∧
      (rawCells a (fun i ↦ (a i).left)).IsCardinalAccessible κ ∧
      (rawCells a (fun i ↦ (a i).right)).IsCardinalAccessible κ := by
  have := locallyPresentable_hasColimits (C := C)
  obtain ⟨κ, hκ, ha⟩ := exists_common_arrow_presentability a
  have : ∀ i, IsCardinalPresentable (a i).left κ := fun i ↦ (ha i).1
  have : ∀ i, IsCardinalPresentable (a i).right κ := fun i ↦ (ha i).2
  exact ⟨κ, hκ, squareFamily_isCardinalAccessible_of_endpoints a κ,
    rawCells_isCardinalAccessible a _ κ, rawCells_isCardinalAccessible a _ κ⟩

example [HasColimitsOfSize.{w, w} C] (a : ι → Arrow C) (A : ι → C) :
    cells a A ≅ rawCells a A := cellsIsoRaw a A

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.HomotopicalAlgebra.Smith.DependentCopower,
        `SerrePositivity.HomotopicalAlgebra.Smith.AccessibleSquares].contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  if modules.size != 2 then throwError "Not all square-accessibility modules were audited"
  logInfo m!"Accessible square audit passed: {count} declarations in 2 modules, standard axioms only."
