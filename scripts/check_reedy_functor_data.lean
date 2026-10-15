import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorData
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
import Lean.Util.CollectAxioms

universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {C : Type u'} [Category.{v'} C]

example (d : FunctorData r C) : J ⥤ C := d.toFunctor

example (d : FunctorData r C) {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    d.toFunctor.map (f ≫ g) = d.toFunctor.map f ≫ d.toFunctor.map g := d.toFunctor.map_comp f g

example (d : FunctorData r C) {i j : J} (f : i ⟶ j) (hf : inverse f) :
    d.toFunctor.map f = d.mapInverse f hf := d.toFunctor_map_inverse f hf

example (d : FunctorData r C) {i j : J} (f : i ⟶ j) (hf : direct f) :
    d.toFunctor.map f = d.mapDirect f hf := d.toFunctor_map_direct f hf

-- Reconstruction is tested against an existing actual functor on all morphisms.
example (F : SimplexCategory ⥤ C) {i j : SimplexCategory} (f : i ⟶ j) :
    (FunctorData.ofFunctor simplex F).toFunctor.map f = F.map f :=
  FunctorData.ofFunctor_toFunctor_map simplex F f

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorData do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Reedy functor-data module was not audited"
  logInfo m!"Reedy functor-data audit passed: {count} declarations, standard axioms only."
