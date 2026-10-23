import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallReference

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- No value model structure is used for any of the whole-space comparisons.
example (K P : SSet.{v}) : SimplexParameterHom.obj K P ≅ (ihom K).obj P :=
  SimplexParameterHom.nativeIso K P

example (K P : SSet.{v}) (hP : SSet.modelCategoryQuillen.J.rlp (terminal.from P)) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (SimplexParameterHom.obj K P)) :=
  SimplexParameterHom.kan K P hP

example (K P : SSet.{v}) :
    SSet.uliftFunctor.{w, v}.obj (SimplexParameterHom.obj K P) ≅
      SimplexParameterHom.obj (UniverseLift.obj.{w} K) (UniverseLift.obj.{w} P) :=
  UniverseLiftParameterHom.iso K P

example : SimplexParameterHom.bifunctor.{v} ⋙ SSet.uliftFunctor.{w, v} ≅
    (SSet.uliftFunctor.{w, v}.op.prod SSet.uliftFunctor.{w, v}) ⋙
      SimplexParameterHom.bifunctor.{max w v} :=
  UniverseLiftParameterHom.bifunctorIso

example (K P : SSet.{v}) : SSet.uliftFunctor.{w, v}.obj ((ihom K).obj P) ≅
    (ihom (UniverseLift.obj.{w} K)).obj (UniverseLift.obj.{w} P) :=
  UniverseLiftParameterHom.closedIso K P

example (K P Q : SSet.{v}) :
    (UniverseLift.tensorIso.{w} (SimplexParameterHom.obj K P)
        (SimplexParameterHom.obj P Q)).inv ≫
      SSet.uliftFunctor.{w, v}.map (SimplexParameterHom.composition K P Q) ≫
        (UniverseLiftParameterHom.iso K Q).hom =
    ((UniverseLiftParameterHom.iso K P).hom ⊗ₘ (UniverseLiftParameterHom.iso P Q).hom) ≫
      SimplexParameterHom.composition (UniverseLift.obj.{w} K) (UniverseLift.obj.{w} P)
        (UniverseLift.obj.{w} Q) :=
  UniverseLiftParameterHom.composition K P Q

example (K : SSet.{v}) (n : SimplexCategory) :
    UniverseLift.simplexTensorMap.{w, v} (SimplexParameterHom.identityFamily K n) =
      SimplexParameterHom.identityFamily (UniverseLift.obj.{w} K) n :=
  UniverseLiftParameterHom.identity K n

-- Apply the full mapping-space result to the actual small Kan references on the base.
section References
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (b c : Cᵒᵖ × C)

example : SSet.modelCategoryQuillen.J.rlp (terminal.from (SimplexParameterHom.obj
    (OrdinaryBarSmallReference.value hcof hfib b)
    (OrdinaryBarSmallReference.value hcof hfib c))) :=
  SimplexParameterHom.kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib c)

example : SSet.uliftFunctor.{max u v, v}.obj (SimplexParameterHom.obj
      (OrdinaryBarSmallReference.value hcof hfib b)
      (OrdinaryBarSmallReference.value hcof hfib c)) ≅
    SimplexParameterHom.obj
      (UniverseLift.obj.{max u v} (OrdinaryBarSmallReference.value hcof hfib b))
      (UniverseLift.obj.{max u v} (OrdinaryBarSmallReference.value hcof hfib c)) :=
  UniverseLiftParameterHom.iso _ _
end References

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom]
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
  unless modules.size == expected.size do
    throwError "Missing universe-lift parameter Hom modules"
  logInfo m!"Universe-lift parameter Hom audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
