import SerrePositivity.Spectra.ModelCategory.SimplicialMonoidal
import SerrePositivity.Spectra.General.Foundations
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms

universe u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Quillen SerrePositivity.SimplicialModelInputs
open SerrePositivity.InfinityCategories.HA.ModelCategoryComparison (CofibrantlyGenerated)

example {A B X Y : SSet.{u}} (i : A ⟶ B) (j : X ⟶ Y) [Mono i] [Mono j]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) : Mono sq.ι :=
  _root_.SerrePositivity.SimplicialModel.simplicial_pushoutProduct_mono i j sq

-- The model and its two class equalities are explicit inputs. No existence
-- axiom, weak-equivalence definition, or monoidal-model hypothesis is assumed.
section
variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

example : SSet.anodyneExtensions.{u} = trivialCofibrations SSet.{u} :=
  _root_.SerrePositivity.SimplicialModel.simplicial_anodyne_eq_trivialCofibrations hFib
example : CofibrantlyGenerated.{u}
    SSet.modelCategoryQuillen.I.{u} SSet.modelCategoryQuillen.J.{u} :=
  _root_.SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hCof hFib
example : IsQuillenBifunctor (curriedTensor SSet.{u}) :=
  _root_.SerrePositivity.SimplicialModel.simplicial_isQuillenBifunctor hCof hFib
example : MonoidalModelCategory SSet.{u} := _root_.SerrePositivity.SimplicialModel.simplicial_monoidalModel hCof hFib
example : HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{u})) :=
  _root_.SerrePositivity.SimplicialModel.simplicial_SM7 hCof hFib
example : MonoidalModelCategory PointedSimplicialSet.{u} :=
  pointedSimplicial_monoidalModel hCof hFib
example : HasQuillenPullbackHom
    (MonoidalClosed.internalHom (C := PointedSimplicialSet.{u})) :=
  pointedSimplicial_SM7 hCof hFib
end

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.Spectra.ModelCategory.SimplicialMonoidal do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No simplicial monoidal declarations audited"
  logInfo m!"Simplicial monoidal audit passed: {count} declarations, standard axioms only."
