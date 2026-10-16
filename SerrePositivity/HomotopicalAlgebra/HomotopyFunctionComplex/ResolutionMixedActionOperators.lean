module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction

/-! # All external simplex operators on the same small mixed triangle and facet actions -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedSmallFamilies ResolutionMixedSmallAction

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedActionOperators
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev inputMap {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C) :=
  NerveSmallAction.inputMap C (cornerD C) c θ Z
abbrev outputMap {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C) :=
  NerveSmallAction.outputMap C hcof hfib (cornerD C) c θ Z

/-- Every external face and degeneracy uses the actual final cube's two resolution maps. -/
lemma action_operator (side : Bool) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z) :
    NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ action C hcof hfib side c Z t =
    ResolutionArrowActionTransport.kan C hcof hfib
      ((cornerD C).obj ((NerveSmallAction.reindexChain c θ).obj (Fin.last m))) Z
      (NerveSmallAction.prefixParameter (smallParameter C) c θ ≫
        family C hcof hfib side (NerveSmallAction.reindexChain c θ))
      ((NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ t) ≫ inputMap C c θ Z) ≫
        outputMap C hcof hfib c θ Z :=
  NerveSmallAction.operator C hcof hfib (cornerD C) (smallParameter C)
    (system C hcof hfib side) c θ Z t

lemma action_operator_of_input (side : Bool) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : chainParameter C c ⟶ input C (c.obj (Fin.last n)) Z)
    (t' : chainParameter C (NerveSmallAction.reindexChain c θ) ⟶
      input C ((NerveSmallAction.reindexChain c θ).obj (Fin.last m)) Z)
    (ht : (NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ t) ≫ inputMap C c θ Z =
      NerveSmallAction.prefixParameter (smallParameter C) c θ ≫ t') :
    NerveSmallAction.operatorParameter (smallParameter C) c θ ≫ action C hcof hfib side c Z t =
    (NerveSmallAction.prefixParameter (smallParameter C) c θ ≫
      action C hcof hfib side (NerveSmallAction.reindexChain c θ) Z t') ≫
        outputMap C hcof hfib c θ Z :=
  NerveSmallAction.operator_of_input C hcof hfib (cornerD C) (smallParameter C)
    (system C hcof hfib side) c θ Z t t' ht

/-- The same operator law holds for every one of the already fixed whole facet systems. -/
lemma faceAction_operator_of_input (side : Bool) (k : Fin 3) {n m : ℕ}
    (c : ComposableArrows (Index C) n) (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : faceParameter C c ⟶ input C (c.obj (Fin.last n)) Z)
    (t' : faceParameter C (NerveSmallAction.reindexChain c θ) ⟶
      input C ((NerveSmallAction.reindexChain c θ).obj (Fin.last m)) Z)
    (ht : (NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫ t) ≫
      inputMap C c θ Z = NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫ t') :
    NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫
      faceAction C hcof hfib side k c Z t =
    (NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫
      faceAction C hcof hfib side k (NerveSmallAction.reindexChain c θ) Z t') ≫
        outputMap C hcof hfib c θ Z :=
  NerveSmallAction.operator_of_input C hcof hfib (cornerD C) (smallIntervalParameter C)
    (faceSystem C hcof hfib side k) c θ Z t t' ht

omit [ModelCategory SSet.{v}] in
lemma face_prefix (k : Fin 3) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫
      ((smallFaceMap C k).app (c.obj (θ.toOrderHom 0)) ▷
        SSet.stdSimplex.obj (SimplexCategory.mk m)) =
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk m)) ≫
      NerveSmallAction.prefixParameter (smallParameter C) c θ := by
  change _ ▷ _ ≫ _ ▷ _ = _ ▷ _ ≫ _ ▷ _
  rw [← comp_whiskerRight, ← comp_whiskerRight]
  exact congrArg (fun f => f ▷ SSet.stdSimplex.obj (SimplexCategory.mk m))
    ((smallFaceMap C k).naturality (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))))

omit [ModelCategory SSet.{v}] in
lemma face_operator (k : Fin 3) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk m)) ≫
      NerveSmallAction.operatorParameter (smallParameter C) c θ =
    NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫
      ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) :=
  whisker_exchange ((smallFaceMap C k).app (c.obj 0)) (SSet.stdSimplex.{v}.map θ)

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedActionOperators
