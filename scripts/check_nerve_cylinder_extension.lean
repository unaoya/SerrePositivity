import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.Reedy
open NerveCylinderBoundary NerveCylinderExtension

section ChangingBothEnds
variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  (K F G : D ⥤ SSet.{w}) (H : E ⥤ D) (p : F ⟶ G)
  (a : NerveBiparameter.System K F)

example : NerveBiparameter.System (H ⋙ K) (H ⋙ G) :=
  NerveBiparameterMaps.reindex K G H (NerveBiparameterMaps.mapTarget K F G p a)
end ChangingBothEnds

section WholeCylinder
-- Independent indexing universes; only the small values supply boundary fillers.
variable {D : Type uD} [Category.{vD} D]
  (V K : D ⥤ SSet.{max w v}) (i : V ⟶ K)
  {A T : SSet.{max w v}} (j : A ⟶ T) (F : D ⥤ SSet.{v})
  (hi : ∀ d, Mono (i.app d)) [Mono j]
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d))
  (b : NerveMovingParameter.System (product K A) F)
  (c : NerveMovingParameter.System (product V T) F)
  (h : b ≫ NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F)
      (horizontal V K i A) =
    c ≫ NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F) (vertical j V))
  (n : ℕ) (old : NerveMovingParameter.LowerSystem (product K T) F n)
  (hboundary : old ≫ Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (NerveMovingParameterRelative.restriction (boundary V K i j) (product K T)
        (inclusion V K i j) F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (system V K i j (NerveMovingParameter.lifted F) b c h))

example (d : D) : Mono ((inclusion V K i j).app d) := inclusion_mono V K i j hi d

-- Both entire coherent systems stay fixed, at all external faces and degeneracies.
example : extend V K i j F hi hp b c h n old hboundary ≫
    NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F) (vertical j K) = b :=
  extend_endpoints V K i j F hi hp b c h n old hboundary

example : extend V K i j F hi hp b c h n old hboundary ≫
    NerveBiparameterMaps.restriction _ _ (NerveMovingParameter.lifted F)
      (horizontal V K i T) = c :=
  extend_vertices V K i j F hi hp b c h n old hboundary

-- The prescribed complete lower families also stay fixed.
example : Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
    (extend V K i j F hi hp b c h n old hboundary) = old :=
  extend_restrict V K i j F hi hp b c h n old hboundary

-- At external degree zero, each entire old interval family is recovered as the actual map.
example (families : ∀ d, (product K T).obj d ⟶ UniverseLift.obj.{w} (F.obj d))
    (hfamilies : NerveMovingParameter.vertices (product K T) F families ≫
        Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
          (NerveMovingParameterRelative.restriction (boundary V K i j) (product K T)
            (inclusion V K i j) F) =
      Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) 1)
        (system V K i j (NerveMovingParameter.lifted F) b c h)) (d : D) :
    NerveMovingParameter.evaluate (product K T) F
      (extend V K i j F hi hp b c h 1
        (NerveMovingParameter.vertices (product K T) F families) hfamilies) d = families d :=
  NerveMovingParameterRelative.extendFamilies_evaluate _ _ _ _ _ _ _ _ _ d

-- Concrete interval boundary uses the very same construction, without an extra mono input.
example (d : D) : Mono ((inclusion V K i (SSet.boundary.{max w v} 1).ι).app d) :=
  inclusion_mono V K i _ hi d
end WholeCylinder

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterMaps,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.PushoutCotensor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NervePushoutBoundary,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveCylinderBoundary,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagramTensor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveCylinderExtension]
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
    throwError "Some moving cylinder boundary modules were not audited"
  logInfo m!"Moving cylinder boundary audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
