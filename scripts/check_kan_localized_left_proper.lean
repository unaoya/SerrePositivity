import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

variable {A B C P K : SSet.{max u v}}

example {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    SSet.Homotopy ((MonoidalClosed.pre f).app K) ((MonoidalClosed.pre g).app K) :=
  PrecompositionHomotopy.homotopy H K

-- The actual precomposition image is fixed for the entire interval, without a Kan target.
example (p : A ⟶ B) (s : B ⟶ A) (H : SSet.Homotopy (𝟙 A) (p ≫ s))
    (hH : H.h ≫ p = fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p) :
    ((MonoidalClosed.pre p).app K) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
      (MappingPrecompositionRetraction.homotopy p s H K).h =
    fst ((ihom B).obj K) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      (MonoidalClosed.pre p).app K := MappingPrecompositionRetraction.fixed p s H hH K

example (f : A ⟶ B)
    (h : Function.Bijective (HomotopyClasses.post ((MonoidalClosed.pre f).app K)
      (X := 𝟙_ SSet.{max u v}))) :
    Function.Bijective (HomotopyClasses.pre f (K := K)) :=
  HomotopyRetractionTests.pre_bijective_of_restriction_post f h

variable (f : A ⟶ B) (j : A ⟶ C) [Mono j] (r : B ⟶ P) (s : C ⟶ P)
  (sq : IsPushout f j r s)

-- An actual pushout, not an isomorphic chosen replacement.
example : IsPullback ((MonoidalClosed.pre r).app K) ((MonoidalClosed.pre s).app K)
    ((MonoidalClosed.pre f).app K) ((MonoidalClosed.pre j).app K) :=
  PushoutInternalHomPullback.isPullback sq K

-- The boundary-right case does not assume any of the original objects Kan.
example (hf : (MorphismProperty.monomorphisms SSet.{max u v}).rlp f) :
    IsIso (AnodyneHomotopy.anodyneQ.map s) :=
  MonoRightPushoutEquivalence.localized_isIso f hf j r s sq

-- f itself can be nonmono. Only the other pushout leg j is mono.
example (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map s) :=
  KanLocalizedLeftProper.localized_isIso f hf j r s sq

example (hf : IsIso (AnodyneHomotopy.anodyneQ.map f))
    {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map s) :=
  KanLocalizedLeftProper.image_isIso f hf j r s sq L hL

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.PrecompositionHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.PushoutInternalHomPullback,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyRetractionTests,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper]
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
  unless modules.size == expected.size do throwError "Missing Kan localized left properness modules"
  logInfo m!"Kan localized left properness audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
