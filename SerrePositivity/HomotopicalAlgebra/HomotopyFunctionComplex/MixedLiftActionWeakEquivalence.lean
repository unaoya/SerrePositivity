module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance
public import SerrePositivity.HomotopicalAlgebra.Quillen.ContractibleParameters

/-! # Arbitrary whole lift families act by weak equivalences

The universal action has both entire contractible lift spaces as parameters.
Its weak equivalence follows from one strict lift section and two-out-of-three.
Consequently no constancy or strict-lift condition is imposed on the families.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X X' : ResolutionObject C) (f : X.base ⟶ X'.base)
  (Y Y' : ResolutionObject Cᵒᵖ) (g : Y.base ⟶ Y'.base)

abbrev domain : SSet.{v} := ResolutionLiftSpace.obj X X' f ⨯
  (ResolutionLiftSpace.obj Y Y' g ⨯ MixedResolutionLiftAction.input X' Y')

abbrev projection : domain X X' f Y Y' g ⟶ MixedResolutionLiftAction.input X' Y' :=
  prod.snd ≫ prod.snd

abbrev universal : domain X X' f Y Y' g ⟶ MixedResolutionLiftAction.output X Y :=
  MixedResolutionLiftAction.action X X' f Y Y' g prod.fst (prod.snd ≫ prod.fst)
    (projection X X' f Y Y' g)

lemma graph_factor {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ MixedResolutionLiftAction.input X' Y') :
    prod.lift s (prod.lift r t) ≫ universal X X' f Y Y' g =
      MixedResolutionLiftAction.action X X' f Y Y' g s r t := by
  rw [MixedResolutionLiftAction.action_parameter]
  simp only [projection, ← Category.assoc, prod.lift_fst, prod.lift_snd]

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma projection_trivialFibration :
    trivialFibrations SSet.{v} (projection X X' f Y Y' g) :=
  Quillen.ContractibleParameters.double_projection_trivialFibration
    SSet.stdSimplex.isTerminalObj₀ (ResolutionLiftSpace.projection X X' f)
    (ResolutionLiftSpace.projection Y Y' g)
    (ResolutionLiftSpace.projection_trivialFibration hcof X X' f)
    (ResolutionLiftSpace.projection_trivialFibration hcof Y Y' g) _

include hcof in
lemma graph_weakEquivalence {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ MixedResolutionLiftAction.input X' Y')
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v} (prod.lift s (prod.lift r t)) :=
  Quillen.ContractibleParameters.graph_weakEquivalence SSet.stdSimplex.isTerminalObj₀
    (ResolutionLiftSpace.projection X X' f) (ResolutionLiftSpace.projection Y Y' g)
    (ResolutionLiftSpace.projection_trivialFibration hcof X X' f)
    (ResolutionLiftSpace.projection_trivialFibration hcof Y Y' g) s r t ht

variable (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma universal_weakEquivalence (hf : weakEquivalences C f) (hg : weakEquivalences Cᵒᵖ g) :
    weakEquivalences SSet.{v} (universal X X' f Y Y' g) := by
  let k : X ⟶ X' := ResolutionObject.lift f
  let l : Y ⟶ Y' := ResolutionObject.lift g
  let s := SSet.stdSimplex.isTerminalObj₀.from (MixedResolutionLiftAction.input X' Y') ≫
    ResolutionLiftSpace.ofLift k
  let r := SSet.stdSimplex.isTerminalObj₀.from (MixedResolutionLiftAction.input X' Y') ≫
    ResolutionLiftSpace.ofLift l
  have hstrict := MixedResolutionInvariance.strict_action_weakEquivalence hcof hfib k l hf hg
    (SSet.stdSimplex.isTerminalObj₀.from _) (SSet.stdSimplex.isTerminalObj₀.from _)
  change weakEquivalences SSet.{v}
    (MixedResolutionLiftAction.action X X' f Y Y' g s r (𝟙 _)) at hstrict
  rw [← graph_factor] at hstrict
  exact (weakEquivalences SSet.{v}).of_precomp _ _
    (graph_weakEquivalence X X' f Y Y' g hcof s r (𝟙 _)
      ((weakEquivalences SSet.{v}).id_mem _)) hstrict

include hcof hfib in
lemma action_weakEquivalence (hf : weakEquivalences C f) (hg : weakEquivalences Cᵒᵖ g)
    {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ MixedResolutionLiftAction.input X' Y')
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v} (MixedResolutionLiftAction.action X X' f Y Y' g s r t) := by
  rw [← graph_factor]
  exact (weakEquivalences SSet.{v}).comp_mem _ _
    (graph_weakEquivalence X X' f Y Y' g hcof s r t ht)
    (universal_weakEquivalence X X' f Y Y' g hcof hfib hf hg)

include hcof hfib in
lemma kanAction_weakEquivalence (hf : weakEquivalences C f) (hg : weakEquivalences Cᵒᵖ g)
    {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ MixedResolutionLiftAction.input X' Y')
    (ht : weakEquivalences SSet.{v} t) :
    weakEquivalences SSet.{v}
      (MixedResolutionLiftAction.kanAction X X' f Y Y' g hcof hfib s r t) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (action_weakEquivalence X X' f Y Y' g hcof hfib hf hg s r t ht)
    (KanReplacement.unit_weakEquivalence hcof hfib _)

end SerrePositivity.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence
