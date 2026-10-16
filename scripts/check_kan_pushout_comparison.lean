import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

variable {A B E T X Y P Q : SSet.{max u v}}

-- No Kan source, Kan target, or value model structure is assumed.
example (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{max u v}).rlp p) :
    ∃ s : B ⟶ E, s ≫ p = 𝟙 B := MonoRightLiftingContraction.exists_section p hp

example (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{max u v}).rlp p)
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) :
    ∃ H : SSet.Homotopy (𝟙 E) (p ≫ s),
      H.h ≫ p = fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p :=
  MonoRightLiftingContraction.exists_vertical_contraction p hp s hs

-- Actual functorial data, rather than a factorization assumed on the source category.
example : MorphismProperty.FunctorialFactorizationData
    (MorphismProperty.monomorphisms SSet.{max u v}) SSet.modelCategoryQuillen.I.rlp :=
  MonoLocalizedFactorization.factorization

example (f : X ⟶ Y) :
    MonoLocalizedFactorization.left f ≫ MonoLocalizedFactorization.right f = f :=
  MonoLocalizedFactorization.fac f

example (f : X ⟶ Y) : IsIso (AnodyneHomotopy.anodyneQ.map f) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map (MonoLocalizedFactorization.left f)) :=
  (MonoLocalizedFactorization.left_localized_isIso_iff f).symm

-- The comparing arrow itself need not be mono.
example {D : Type uD} [Category.{vD} D] (F : Under A ⥤ D)
    (hF : ∀ {U V : Under A} (f : U ⟶ V), Mono f.right →
      IsIso (AnodyneHomotopy.anodyneQ.map f.right) → IsIso (F.map f))
    {U V : Under A} [Mono U.hom] [Mono V.hom] (f : U ⟶ V)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) : IsIso (F.map f) :=
  UnderMonoBrown.map_isIso F hF f hf

-- Arbitrary base change and two arbitrary actual pushouts, retaining the given comparison m.
example (a : A ⟶ T) (i : A ⟶ X) (j : A ⟶ Y) [Mono i] [Mono j]
    (f : X ⟶ Y) (hf : i ≫ f = j) (hw : IsIso (AnodyneHomotopy.anodyneQ.map f))
    (r : X ⟶ P) (s : T ⟶ P) (sq : IsPushout i a r s)
    (r' : Y ⟶ Q) (s' : T ⟶ Q) (sq' : IsPushout j a r' s')
    (m : P ⟶ Q) (hm : r ≫ m = f ≫ r') (hm' : s ≫ m = s') :
    IsIso (AnodyneHomotopy.anodyneQ.map m) :=
  KanPushoutComparison.actual_localized_isIso a i j f hf hw r s sq r' s' sq' m hm hm'

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UnderMonoBrown,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanPushoutComparison]
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
  unless modules.size == expected.size do throwError "Missing Kan pushout comparison modules"
  logInfo m!"Kan pushout comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
