import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

section GeneralRelativeValues
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{v}]
  (F G : D ⥤ SSet.{v}) (p : F ⟶ G)
  (hp : ∀ d, trivialFibrations SSet.{v} (p.app d))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (target : NerveCoherentFamily.System G) (n : ℕ) (old : NerveLowerExtension.LowerSystem F n)
  (hboundary : old ≫ Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveRelativeValueExtension.valueMap F G p) =
      Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n) target)

-- The entire target system can vary and is fixed in every chain degree.
example : NerveRelativeValueExtension.extend F G p target n old hboundary hp hcof ≫
    NerveRelativeValueExtension.valueMap F G p = target :=
  NerveRelativeValueExtension.extend_boundary F G p target n old hboundary hp hcof
example : Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveRelativeValueExtension.extend F G p target n old hboundary hp hcof) = old :=
  NerveRelativeValueExtension.extend_restrict F G p target n old hboundary hp hcof
end GeneralRelativeValues

section ArbitraryParameter
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{v}] (F : D ⥤ SSet.{v})
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))
  {A K : SSet.{v}} (i : A ⟶ K) [Mono i] (boundary : NerveParameterExtension.System F A)
  (families : ∀ d, K ⟶ F.obj d)
  (hfamilies : NerveParameterExtension.familyVertices F families ≫
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) 1)
      (NerveRelativeValueExtension.valueMap (NerveParameterExtension.cotensor F K)
        (NerveParameterExtension.cotensor F A) (NerveParameterExtension.restriction F i)) =
          Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) 1) boundary)

-- Every original whole family is recovered as a map K→F(d), not just up to homotopy.
example (d : D) : NerveParameterExtension.evaluate F
    (NerveParameterExtension.extendFamilies F hcof hfib hp i boundary families hfamilies) d =
      families d :=
  NerveParameterExtension.extendFamilies_evaluate F hcof hfib hp i boundary families hfamilies d

-- All previously chosen coherent parameter faces remain fixed in every external degree.
example : NerveParameterExtension.extendFamilies F hcof hfib hp i boundary families hfamilies ≫
    NerveRelativeValueExtension.valueMap (NerveParameterExtension.cotensor F K)
      (NerveParameterExtension.cotensor F A) (NerveParameterExtension.restriction F i) = boundary :=
  NerveParameterExtension.extendFamilies_boundary F hcof hfib hp i boundary families hfamilies
end ArbitraryParameter

section ActualOldMixedEdge
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

private abbrev F := MixedChoiceFunctor.existingFunctor Y W g hcof
private abbrev oldEdge (t : MixedChoiceFunctor.Context Y W) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ (F hcof Y W g).obj t :=
  CoherentLiftMixedComparison.edgeAB hcof hfib t.1.unop.left.inner Y.inner W t.2.right
    t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom)

include hfib in
private lemma hp (t : MixedChoiceFunctor.Context Y W) :
    trivialFibrations SSet.{v} ((NerveCoherentExtension.projection (F hcof Y W g)).app t) := by
  have he : (NerveCoherentExtension.projection (F hcof Y W g)).app t =
      (MixedChoiceFunctor.choiceIso Y W g hcof t).inv ≫
        (MixedChoiceFunctor.projection Y W g hcof).app t :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact (trivialFibrations SSet.{v}).comp_mem _ _
    ((trivialFibrations SSet.{v}).of_isIso (MixedChoiceFunctor.choiceIso Y W g hcof t).inv)
    (MixedChoiceFunctor.projection_trivialFibration Y W g hcof hfib t)

variable
  (boundary : NerveParameterExtension.System (F hcof Y W g) (SSet.boundary.{v} 1).toSSet)
  (hboundary : NerveParameterExtension.familyVertices (F hcof Y W g) (oldEdge hcof hfib Y W g) ≫
    Functor.whiskerLeft (Reedy.lowerInclusion
      (NerveCoherentFamily.reedy (MixedChoiceFunctor.Context Y W)) 1)
      (NerveRelativeValueExtension.valueMap
        (NerveParameterExtension.cotensor (F hcof Y W g)
          (SSet.stdSimplex.obj (SimplexCategory.mk 1)))
        (NerveParameterExtension.cotensor (F hcof Y W g) (SSet.boundary 1).toSSet)
        (NerveParameterExtension.restriction (F hcof Y W g) (SSet.boundary 1).ι)) =
          Functor.whiskerLeft (Reedy.lowerInclusion
            (NerveCoherentFamily.reedy (MixedChoiceFunctor.Context Y W)) 1) boundary)

-- A compatible coherent endpoint system permits the actual old edgeAB to be retained whole.
example (t : MixedChoiceFunctor.Context Y W) : NerveParameterExtension.evaluate (F hcof Y W g)
    (NerveParameterExtension.extendFamilies (F hcof Y W g) hcof hfib (hp hcof hfib Y W g)
      (SSet.boundary 1).ι boundary (oldEdge hcof hfib Y W g) hboundary) t =
        CoherentLiftMixedComparison.edgeAB hcof hfib t.1.unop.left.inner Y.inner W t.2.right
          t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) :=
  NerveParameterExtension.extendFamilies_evaluate _ _ _ _ _ _ _ _ t
end ActualOldMixedEdge

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNaturalMatching,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveRelativeValueExtension,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveParameterExtension]
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
    throwError "Some mixed choice modules were not audited"
  logInfo m!"Coherent parameter extension audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
