import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u w vJ uJ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

-- Arbitrary covariant type-valued functor; no full/object-injective projection assumption.
section GeneralReedy
variable {J : Type uJ} [Category.{vJ} J] (P : J ⥤ Type w)
  {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)
example : ReedyStructure (Reedy.elementsInverse (inverse := inverse) P)
    (Reedy.elementsDirect (direct := direct) P) ℕ := Reedy.elementsReedy P r
example {x y : P.Elements} (f : x ⟶ y) :
    Nonempty (Unique (MorphismProperty.MapFactorizationData
      (Reedy.elementsInverse (inverse := inverse) P)
      (Reedy.elementsDirect (direct := direct) P) f)) :=
  (Reedy.elementsReedy P r).nonempty_unique f
end GeneralReedy

section Coherence
variable {D : Type u} [Category.{v} D] (F : D ⥤ SSet.{w})
example : Index D ⥤ D := NerveSimplexEndpoint.functor D
example : Index D ⥤ SSet.{w} := NerveCoherentFamily.simplices D
example (s : Index D) : (NerveCoherentFamily.reedy D).deg s = dimension s :=
  NerveCoherentFamily.reedy_degree D s
example {s t : Index D} (f : s ⟶ t) (hf : NerveCoherentFamily.inverse D f) :
    IsIso ((NerveSimplexEndpoint.functor D).map f) := NerveCoherentFamily.endpointMap_isIso f hf

-- Arbitrary chain lengths and simplex operators; endpoint movement is included.
example (a : NerveCoherentFamily.System F) {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ a.app (ofChain c) =
      a.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
        F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveCoherentFamily.reindex_compatibility F a c θ

-- Deleting the last endpoint uses the actual arrow, rather than an identity map.
example {x y : D} (f : x ⟶ y) :
    endpointMap (reindexArrow (ComposableArrows.mk₁ f) (SimplexCategory.δ (1 : Fin 2))) = f := by
  rw [reindexArrow_endpoint]
  rfl
example {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    endpointMap (reindexArrow (ComposableArrows.mk₂ f g) (SimplexCategory.δ (2 : Fin 3))) = g := by
  rw [reindexArrow_endpoint]
  rfl
example (p : (Functor.const D).obj (SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0)) ⟶ F) :
    NerveCoherentFamily.System F := NerveCoherentFamily.ofPoint F p
end Coherence

section ActualMixedBaseline
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

-- The old pointA provides one baseline on every external context chain.
example : NerveCoherentFamily.System (MixedChoiceFunctor.existingFunctor Y W g hcof) :=
  NerveCoherentFamily.ofPoint (MixedChoiceFunctor.existingFunctor Y W g hcof)
    (MixedChoiceFunctor.existingPoint Y W g hcof)
end ActualMixedBaseline

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.NerveSimplexEndpoint,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Elements,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentFamily]
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
  logInfo m!"Nerve coherent family audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
