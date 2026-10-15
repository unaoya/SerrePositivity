import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBoundary
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorPushout
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexResolution
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : SimplexCategory ⥤ C)

example : FiniteTensor.FiniteNonsingular.{v} ⥤ C := FiniteTensor.functor A

-- Arbitrary maps, without a monomorphism or fixed-ambient assumption.
example {X Y : SSet.{v}} [X.Finite] [X.Nonsingular] [Y.Finite] [Y.Nonsingular]
    (f : X ⟶ Y) : FiniteTensor.obj A X ⟶ FiniteTensor.obj A Y := FiniteTensor.map A f

example : FiniteTensor.standardDiagram.{v} ⋙ FiniteTensor.functor A ≅ A :=
  FiniteTensor.standardIso A

example {n m : SimplexCategory} (f : n ⟶ m) :
    FiniteTensor.map A (SSet.stdSimplex.{v}.map f) ≫
        FiniteTensor.representationMap A (SSet.stdSimplex.obj m) (Iso.refl _) =
      FiniteTensor.representationMap A (SSet.stdSimplex.obj n) (Iso.refl _) ≫ A.map f :=
  FiniteTensor.standard_naturality A f

example {X₁ X₂ X₃ X₄ : SSet.{v}}
    [X₁.Finite] [X₁.Nonsingular] [X₂.Finite] [X₂.Nonsingular]
    [X₃.Finite] [X₃.Nonsingular] [X₄.Finite] [X₄.Nonsingular]
    {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {i : X₂ ⟶ X₄} {j : X₃ ⟶ X₄}
    (sq : IsPushout f g i j) :
    IsPushout (FiniteTensor.map A f) (FiniteTensor.map A g)
      (FiniteTensor.map A i) (FiniteTensor.map A j) := FiniteTensor.isPushout A sq

example {n : SimplexCategory} {S T : (SSet.stdSimplex.{v}.obj n).Subcomplex} (h : S ≤ T) :
    SubcomplexTensor.map A h = FiniteTensor.map A (SSet.Subcomplex.homOfLE h) := rfl

example (n : ℕ) (i : Fin (n + 2)) :
    FiniteTensor.obj A (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)) ≅
      SubcomplexTensor.obj (SSet.stdSimplex.face {i}ᶜ) A :=
  FiniteTensor.iso A (SSet.stdSimplex.faceSingletonComplIso i)

-- The general finite tensor sends actual boundary generators to cofibrations
-- for the ordinary resolution of every source model category.
example [ModelCategory C] (X : C) (n : ℕ) :
    cofibrations C (FiniteTensor.map
      (SerrePositivity.Reedy.cosimplicialResolution X).obj (SSet.boundary.{v} n).ι) :=
  finiteTensor_boundary_cofibration _ (SerrePositivity.Reedy.cosimplicialResolution X).cofibrant n

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorPushout,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorRepresentable,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBoundary]
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
  logInfo m!"General finite tensor audit passed: {count} declarations in {seen.size} modules."
