import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u w uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

-- The parameter argument works in any model category, without simplicial enrichment.
example {M : Type u} [Category.{v} M] [ModelCategory M] [HasBinaryProducts M]
    {P R Z T V : M} (hZ : IsTerminal Z) (p : P ⟶ Z) (q : R ⟶ Z)
    (hp : trivialFibrations M p) (hq : trivialFibrations M q)
    (s : T ⟶ P) (r : T ⟶ R) (t : T ⟶ V) (ht : weakEquivalences M t) :
    weakEquivalences M (prod.lift s (prod.lift r t)) :=
  SerrePositivity.Quillen.ContractibleParameters.graph_weakEquivalence hZ p q hp hq s r t ht

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X X' : ResolutionObject C) (f : X.base ⟶ X'.base)
  (Y Y' : ResolutionObject Cᵒᵖ) (g : Y.base ⟶ Y'.base)

-- The projection is proved to be a trivial fibration, not assumed a weak equivalence.
example : trivialFibrations SSet.{v}
    (MixedLiftActionWeakEquivalence.projection X X' f Y Y' g) :=
  MixedLiftActionWeakEquivalence.projection_trivialFibration X X' f Y Y' g hcof

-- The universal action retains the full two lift spaces.
example (hf : weakEquivalences C f) (hg : weakEquivalences Cᵒᵖ g) :
    weakEquivalences SSet.{v} (MixedLiftActionWeakEquivalence.universal X X' f Y Y' g) :=
  MixedLiftActionWeakEquivalence.universal_weakEquivalence X X' f Y Y' g hcof hfib hf hg

-- Arbitrary families over the entire input act by weak equivalences.
example (hf : weakEquivalences C f) (hg : weakEquivalences Cᵒᵖ g)
    (s : MixedResolutionLiftAction.input X' Y' ⟶ ResolutionLiftSpace.obj X X' f)
    (r : MixedResolutionLiftAction.input X' Y' ⟶ ResolutionLiftSpace.obj Y Y' g) :
    weakEquivalences SSet.{v}
      (MixedResolutionLiftAction.action X X' f Y Y' g s r (𝟙 _)) :=
  MixedLiftActionWeakEquivalence.action_weakEquivalence X X' f Y Y' g hcof hfib hf hg
    s r (𝟙 _) ((weakEquivalences SSet.{v}).id_mem _)

example (hf : weakEquivalences C f) (hg : weakEquivalences Cᵒᵖ g)
    {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ MixedResolutionLiftAction.input X' Y')
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v}
      (MixedResolutionLiftAction.kanAction X X' f Y Y' g hcof hfib s r t) :=
  MixedLiftActionWeakEquivalence.kanAction_weakEquivalence X X' f Y Y' g
    hcof hfib hf hg s r t ht

-- Both supplied whole systems and all chain simplices use the original action.
example {D : Type uD} [Category.{vD} D] (H : D ⥤ MixedResolutionCenters.Index C)
    (K : D ⥤ SSet.{v})
    (a : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.leftChoices C))
    (b : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.rightChoices C))
    {n : ℕ} (c : ComposableArrows D n)
    (hs : weakEquivalences C
      (ResolutionArrowDiagram.arrow C (NerveMixedAction.center C H c).1))
    (htarget : weakEquivalences Cᵒᵖ
      (ResolutionArrowDiagram.arrow Cᵒᵖ (NerveMixedAction.center C H c).2))
    (t : NerveMixedAction.parameter K c ⟶ NerveMixedAction.input C H c)
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v} (NerveMixedAction.action C hcof hfib H K a b c t) :=
  MixedCenterActionWeakEquivalence.chain_action_weakEquivalence C hcof hfib H K a b c
    hs htarget t ht

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.ContractibleParameters,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionInvariance,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence]
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
    throwError "Some mixed lift action weak equivalence modules were not audited"
  logInfo m!"Mixed lift action weak equivalence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
