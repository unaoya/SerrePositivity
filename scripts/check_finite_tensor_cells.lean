import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorSkeleton
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C]

-- Coproduct preservation needs only finite colimits, without model structure.
example [HasFiniteColimits C] (A : SimplexCategory ⥤ C) {ι : Type v} [Finite ι]
    (X : ι → SSet.{v}) [∀ i, (X i).Finite] [∀ i, (X i).Nonsingular] :
    FiniteTensor.obj A (∐ X) ≅ ∐ (fun i ↦ FiniteTensor.obj A (X i)) :=
  FiniteTensor.coproductIso A X

-- Ordinary resolutions of an arbitrary model category; no chosen functorial
-- factorization or infinite colimits in C are required as extra hypotheses.
example [ModelCategory C] (Z : C) {X Y : SSet.{v}}
    [X.Finite] [X.Nonsingular] [Y.Finite] [Y.Nonsingular] (i : X ⟶ Y) [Mono i] :
    cofibrations C (FiniteTensor.map (SerrePositivity.Reedy.cosimplicialResolution Z).obj i) :=
  FiniteTensor.map_mono_cofibration _
    (SerrePositivity.Reedy.cosimplicialResolution Z).cofibrant i

example [ModelCategory C] (Z : C) (n : ℕ) (i : Fin (n + 2)) :
    cofibrations C (SubcomplexTensor.inclusion (SSet.horn.{v} (n + 1) i)
      (SerrePositivity.Reedy.cosimplicialResolution Z).obj) :=
  subcomplexTensor_cofibration _ (SerrePositivity.Reedy.cosimplicialResolution Z).cofibrant _

-- Relative monomorphisms of subcomplexes, with different endpoints.
example [ModelCategory C] (Z : C) {n : SimplexCategory}
    {S T : (SSet.stdSimplex.{v}.obj n).Subcomplex} (h : S ≤ T) :
    cofibrations C (SubcomplexTensor.map (SerrePositivity.Reedy.cosimplicialResolution Z).obj h) :=
  FiniteTensor.map_mono_cofibration _
    (SerrePositivity.Reedy.cosimplicialResolution Z).cofibrant (SSet.Subcomplex.homOfLE h)

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NonsingularCoproduct,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorCoproduct,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorSkeleton]
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
  logInfo m!"Finite tensor cells audit passed: {count} declarations in {seen.size} modules."
