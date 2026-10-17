import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section GeneralFiber
variable {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}} (p : F ⟶ G)
  (b : (Functor.const D).obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ⟶ G)
  {K : SSet.{v}} (a : (Functor.const D).obj K ⟶ F)
  (ha : ∀ X, a.app X ≫ p.app X = SSet.stdSimplex.isTerminalObj₀.from K ≫ b.app X)

-- No model or assumptions on the arrows; object/Hom universes remain independent.
example : D ⥤ SSet.{v} := FiberFunctor.functor p b
example : (Functor.const D).obj K ⟶ FiberFunctor.functor p b :=
  FiberFunctor.liftFamily p b a ha
end GeneralFiber

section ActualMixed
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

example : (Over Y)ᵒᵖ × Under W ⥤ SSet.{v} := MixedChoiceFunctor.fibers Y W g
example (t : MixedChoiceFunctor.Context Y W) :
    (MixedChoiceFunctor.fibers Y W g).obj t ≅
      ResolutionLiftSpace.obj t.1.unop.left.inner t.2.right (MixedChoiceFunctor.total Y W g t) :=
  MixedChoiceFunctor.fiberIso Y W g t

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example : (Over Y)ᵒᵖ × Under W ⥤ SSet.{v} := MixedChoiceFunctor.functor Y W g hcof
example : MixedChoiceFunctor.point Y W g hcof ≫ MixedChoiceFunctor.projection Y W g hcof = 𝟙 _ :=
  MixedChoiceFunctor.point_projection Y W g hcof
example (t : MixedChoiceFunctor.Context Y W) :
    trivialFibrations SSet.{v} ((MixedChoiceFunctor.projection Y W g hcof).app t) :=
  MixedChoiceFunctor.projection_trivialFibration Y W g hcof hfib t
example (t : MixedChoiceFunctor.Context Y W) :
    weakEquivalences SSet.{v} ((MixedChoiceFunctor.point Y W g hcof).app t) :=
  MixedChoiceFunctor.point_weakEquivalence Y W g hcof hfib t

-- Both source and target move; the two orders agree as actual simplicial maps.
example {a b : (Over Y)ᵒᵖ} {c d : Under W} (k : a ⟶ b) (l : c ⟶ d) :
    (MixedChoiceFunctor.functor Y W g hcof).map (show (a, c) ⟶ (b, c) from (k, 𝟙 c)) ≫
        (MixedChoiceFunctor.functor Y W g hcof).map (show (b, c) ⟶ (b, d) from (𝟙 b, l)) =
      (MixedChoiceFunctor.functor Y W g hcof).map (show (a, c) ⟶ (a, d) from (𝟙 a, l)) ≫
        (MixedChoiceFunctor.functor Y W g hcof).map (show (a, d) ⟶ (b, d) from (k, 𝟙 d)) :=
  MixedChoiceFunctor.interchange Y W g hcof k l
end ActualMixed

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.FiberFunctor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedChoiceFunctor]
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
  logInfo m!"Mixed choice audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
