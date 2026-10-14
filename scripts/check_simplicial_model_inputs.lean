import SerrePositivity.Spectra.ModelCategory.PointedGenerators
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModelInputs
open SSet.modelCategoryQuillen
open scoped SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

-- No Kan-Quillen ModelCategory or weak-equivalence class is assumed.
example {A B : SSet.{u}} (f : A ⟶ B) (hf : I f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := boundaryGenerator_domain_presentable f hf
example {A B : SSet.{u}} (f : A ⟶ B) (hf : J f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := hornGenerator_domain_presentable f hf
example : I.{u}.HasSmallObjectArgument.{u} := boundaryGenerators_smallObjectArgument
example : J.{u}.HasSmallObjectArgument.{u} := hornGenerators_smallObjectArgument
example (X : SSet.{u}) : IsCofibrant X := simplicialSet_isCofibrant X
example (X : PointedSimplicialSet.{u}) : Mono X.hom := pointed_basepoint_mono X
example (X : PointedSimplicialSet.{u}) : IsCofibrant X := pointedSimplicialSet_isCofibrant X
example : IsCofibrant PointedSimplicialSet.circle.{u} := circle_isCofibrant

example : pointedI.{u}.HasSmallObjectArgument.{u} := pointedI_smallObjectArgument
example : pointedJ.{u}.HasSmallObjectArgument.{u} := pointedJ_smallObjectArgument
example {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) (hf : pointedI f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := pointedI_domain_presentable f hf
example {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) (hf : pointedJ f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := pointedJ_domain_presentable f hf
example : pointedI.{u}.rlp = I.rlp.inverseImage PointedSimplicialSet.forget :=
  pointedGenerators_rlp I
example : pointedJ.{u}.rlp = fibrations PointedSimplicialSet.{u} := pointedJ_rlp

example : I.{u}.rlp.llp = MorphismProperty.monomorphisms SSet.{u} :=
  boundaryGenerators_leftClass
example : pointedI.{u}.rlp.llp = cofibrations PointedSimplicialSet.{u} :=
  pointedI_leftClass
example : MorphismProperty.IsWeakFactorizationSystem
    (cofibrations PointedSimplicialSet.{u}) pointedI.rlp := pointedI_weakFactorizationSystem
example : (cofibrations PointedSimplicialSet.{u}).HasFunctorialFactorization pointedI.rlp :=
  pointedI_functorialFactorization

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless #[`SerrePositivity.Spectra.ModelCategory.SimplicialGenerators,
        `SerrePositivity.Spectra.ModelCategory.SimplicialCofibrancy,
        `SerrePositivity.Spectra.ModelCategory.PointedGenerators].contains
        env.header.modules[idx.toNat]!.module do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No concrete simplicial input declarations audited"
  logInfo m!"Concrete simplicial input audit passed: {count} declarations, standard axioms only."
