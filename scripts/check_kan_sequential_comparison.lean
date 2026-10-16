import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.SimplicialModel
open SequentialBoundaryFactorization

-- Actual infinite Arrow colimits in an independent auxiliary value universe.
example {H : ℕ ⥤ Arrow SSet.{max u v}} {c : Cocone H} (hc : IsColimit c)
    (hH : ∀ n, SSet.modelCategoryQuillen.I.rlp (H.obj n).hom) :
    SSet.modelCategoryQuillen.I.rlp c.pt.hom := BoundaryRightColimit.sequential_rlp hc hH

variable {F G : ℕ ⥤ SSet.{max u v}} (α : F ⟶ G)

-- The actual comparison is factored with all original components retained.
example : leftMap α ≫ rightMap α = α := factorization_eq α

example (n : ℕ) : SSet.modelCategoryQuillen.I.rlp ((rightMap α).app n) :=
  right_boundary_rlp α n

variable (hF : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
  (hα : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (α.app n)))

-- Relative successor lifting, not merely objectwise equivalence of the factor.
include hF hα in
example (n : ℕ) : KanTestLiftingClass.rightTests.llp
    (MonoLocalizedFactorization.left (successorArrow α n (stage α n))) := by
  have : Mono (stepMap F n) := hF n
  exact SequentialFactorLiftingClasses.relative_llp α n hα

-- No Kan objects, value model structure, or condition on the target successors is supplied.
include hF hα in
example : IsIso (AnodyneHomotopy.anodyneQ.map (colim.map α)) :=
  KanSequentialColimitComparison.localized_isIso α hF hα

include hF hα in
example (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (m : c.pt ⟶ d.pt) (hm : ∀ n, c.ι.app n ≫ m = α.app n ≫ d.ι.app n) :
    IsIso (AnodyneHomotopy.anodyneQ.map m) :=
  KanSequentialColimitComparison.actual_localized_isIso α hF hα c d hc hd m hm

include hF hα in
example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map (colim.map α)) :=
  KanSequentialColimitComparison.image_isIso α hF hα L hL

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryRightColimit,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SequentialBoundaryFactorization,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SequentialFactorLift,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison]
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
  unless modules.size == expected.size do throwError "Missing Kan sequential comparison modules"
  logInfo m!"Kan sequential comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
