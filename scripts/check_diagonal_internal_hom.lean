import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.BisimplicialModel

-- These comparisons require no model structure or Quillen hypothesis.
example (n m : SimplexCategory) :
    restrictedRepresentable.{v} n m ≅ SSet.stdSimplex.obj n ⊗ SSet.stdSimplex.obj m :=
  restrictedRepresentableIso n m

-- The equivalence computes the actual Kan extension right adjoint's simplices.
example (Z : SSet.{v}) (n m : SimplexCategory) :
    ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m) ≃
      (SSet.stdSimplex.obj n ⊗ SSet.stdSimplex.obj m ⟶ Z) :=
  rightAdjointValueEquiv Z n m

-- The comparison is natural in inner simplex operators, not merely degreewise.
example (Z : SSet.{v}) (n : SimplexCategory) {m' m : SimplexCategory} (g : m' ⟶ m)
    (x : ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m)) :
    rightAdjointValueEquiv Z n m' (((rightAdjoint.obj Z).obj (Opposite.op n)).map g.op x) =
      (SSet.stdSimplex.obj n ◁ SSet.stdSimplex.map g) ≫ rightAdjointValueEquiv Z n m x :=
  rightAdjointValueEquiv_inner Z n g x

-- Outer simplex naturality identifies the entire right adjoint family.
example : rightAdjoint.{v} ≅
    (SSet.stdSimplex.op ⋙ MonoidalClosed.internalHom).flip := rightAdjointInternalHomIso

-- This is an actual ordinary adjunction, with no assumed comparison isomorphism.
example : diagonal.{v} ⊣ (SSet.stdSimplex.op ⋙ MonoidalClosed.internalHom).flip :=
  diagonalInternalHomAdjunction

example {Z Z' : SSet.{v}} (h : Z ⟶ Z') :
    rightAdjoint.map h ≫ rightAdjointInternalHomIso.hom.app Z' =
      rightAdjointInternalHomIso.hom.app Z ≫ internalHomRight.map h :=
  rightAdjointInternalHomIso.hom.naturality h

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRepresentables,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalInternalHom]
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
  unless modules.size == expected.size do throwError "Some diagonal internal Hom modules were not audited"
  logInfo m!"Diagonal internal Hom audit passed: {count} declarations in {modules.size} modules, standard axioms only."
