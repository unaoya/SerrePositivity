import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorPushout
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorRepresentable
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Lean.Util.CollectAxioms

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C)

example {n : SimplexCategory} : (SSet.stdSimplex.{v}.obj n).Subcomplex ⥤ C :=
  SubcomplexTensor.functor A

example {n : SimplexCategory} (S T : (SSet.stdSimplex.{v}.obj n).Subcomplex) :
    IsPushout (SubcomplexTensor.map A (inf_le_left : S ⊓ T ≤ S))
      (SubcomplexTensor.map A (inf_le_right : S ⊓ T ≤ T))
      (SubcomplexTensor.map A (le_sup_left : S ≤ S ⊔ T))
      (SubcomplexTensor.map A (le_sup_right : T ≤ S ⊔ T)) :=
  SubcomplexTensor.isPushout A { sup_eq := rfl, inf_eq := rfl }

-- The concrete decomposition of the two-dimensional middle horn.
example : IsPushout (SubcomplexTensor.map A SSet.horn₂₁.sq.le₁₂)
    (SubcomplexTensor.map A SSet.horn₂₁.sq.le₁₃)
    (SubcomplexTensor.map A SSet.horn₂₁.sq.le₂₄)
    (SubcomplexTensor.map A SSet.horn₂₁.sq.le₃₄) :=
  SubcomplexTensor.isPushout A SSet.horn₂₁.sq

example (n : SimplexCategory) :
    IsIso (SubcomplexTensor.inclusion (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex) A) :=
  inferInstance

example (n : SimplexCategory) :
    IsInitial (SubcomplexTensor.obj (⊥ : (SSet.stdSimplex.{v}.obj n).Subcomplex) A) :=
  SubcomplexTensor.isInitialBot A

example (n : ℕ) (i : Fin (n + 1)) :
    SubcomplexTensor.obj (SSet.stdSimplex.face.{v} {i}) A ≅ A.obj (SimplexCategory.mk 0) :=
  SubcomplexTensor.representationIso A _ (SSet.stdSimplex.faceSingletonIso i)

example (n : ℕ) (i : Fin (n + 2)) :
    SubcomplexTensor.obj (SSet.stdSimplex.face.{v} {i}ᶜ) A ≅ A.obj (SimplexCategory.mk n) :=
  SubcomplexTensor.representationIso A _ (SSet.stdSimplex.faceSingletonComplIso i)

example {n : SimplexCategory} {S T : (SSet.stdSimplex.{v}.obj n).Subcomplex} (h : S ≤ T) :
    SubcomplexTensor.map A h ≫ SubcomplexTensor.inclusion T A =
      SubcomplexTensor.inclusion S A := SubcomplexTensor.map_inclusion A h

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorFunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorPushout,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorRepresentable]
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
  logInfo m!"Tensor gluing audit passed: {count} declarations in {seen.size} modules."
