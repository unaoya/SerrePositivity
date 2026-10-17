import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section LowerSystems
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{v}] (F : D ⥤ SSet.{v})
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (n : ℕ) (a : NerveLowerExtension.LowerSystem F n)

-- All low-degree components, including the full naturality relations, are retained exactly.
example : Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveLowerExtension.extend F hp hcof n a) = a :=
  NerveLowerExtension.extend_restrict F hp hcof n a
example {m : ℕ} (c : ComposableArrows D m) (hm : m < n) :
    (NerveLowerExtension.extend F hp hcof n a).app (NerveSimplexEndpoint.ofChain c) =
      a.app ⟨NerveSimplexEndpoint.ofChain c, hm⟩ :=
  NerveLowerExtension.extend_chain F hp hcof n a c hm

-- This fixes any preassigned system of vertices, edges and triangles below degree 3.
example (a₃ : NerveLowerExtension.LowerSystem F 3) (c : ComposableArrows D 2) :
    (NerveLowerExtension.extend F hp hcof 3 a₃).app (NerveSimplexEndpoint.ofChain c) =
      a₃.app ⟨NerveSimplexEndpoint.ofChain c, Nat.lt_succ_self 2⟩ :=
  NerveLowerExtension.extend_chain F hp hcof 3 a₃ c (Nat.lt_succ_self 2)

-- Point choices need not form a strictly natural transformation on D.
example (points : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj d) (d : D) :
    (NerveLowerExtension.extendVertices F hp hcof points).app
      (NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ d)) = points d :=
  NerveLowerExtension.extendVertices_point F hp hcof points d
end LowerSystems

section ActualOldPointB
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

private abbrev F := MixedChoiceFunctor.existingFunctor Y W g hcof
private abbrev oldB (t : MixedChoiceFunctor.Context Y W) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (F hcof Y W g).obj t :=
  CoherentLiftMixedComparison.pointB hcof t.1.unop.left.inner Y.inner W t.2.right
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

-- The actual previously selected pointB is fixed at every mixed context.
example (t : MixedChoiceFunctor.Context Y W) :
    (NerveLowerExtension.extendVertices (F hcof Y W g) (hp hcof hfib Y W g) hcof
      (oldB hcof Y W g)).app (NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ t)) =
        CoherentLiftMixedComparison.pointB hcof t.1.unop.left.inner Y.inner W t.2.right
          t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) :=
  NerveLowerExtension.extendVertices_point _ _ _ _ t
end ActualOldPointB

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeLifting,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveLowerExtension]
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
  logInfo m!"Lower coherent extension audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
