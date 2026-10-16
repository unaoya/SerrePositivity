module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection

/-! # Evaluation on the actual identity-reference section of the resolution bar

The composite is the lift of the original small mixed action. Its small
map is a weak equivalence; no large simplicial model structure is used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReference
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev reference : OrdinaryBarCenters.Comma R :=
  CostructuredArrow.mk (Y := OrdinaryResolutionPairs.forgetFrames.obj R) (𝟙 _)

abbrev point (n : SimplexCategoryᵒᵖ)
    (x : ((OrdinaryBarEvaluation.raw (C := C)).obj
      (OrdinaryResolutionPairs.forgetFrames.obj R)).obj n) :
    CostructuredArrow (BarConstruction.elementProjection
      (OrdinaryResolutionPairs.projection (C := C)) OrdinaryBarEvaluation.raw n)
      ((OrdinaryResolutionPairs.projection (C := C)).obj
        (OrdinaryResolutionPairs.forgetFrames.obj R)) :=
  CostructuredArrow.mk
    (Y := ((OrdinaryBarEvaluation.raw (C := C)).flip.obj n).elementsMk
      (OrdinaryResolutionPairs.forgetFrames.obj R) x) (𝟙 _)

def sectionMap : UniverseLift.obj.{u} ((OrdinaryBarEvaluation.raw (C := C)).obj
    (OrdinaryResolutionPairs.forgetFrames.obj R)) ⟶
    OrdinaryBarEvaluation.bar R where
  app n := ↾fun x => (Functor.const (Fin (n.unop.len + 1))).obj (point R n x.down)
  naturality {_ _} _ := rfl

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

abbrev smallAction : ((OrdinaryBarEvaluation.raw (C := C)).obj
    (OrdinaryResolutionPairs.forgetFrames.obj R)) ⟶
    OrdinaryBarFirstAction.output R :=
  MixedResolutionCenters.action C (OrdinaryBarCenters.center R (reference R))
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ a.app (ofChain (ComposableArrows.mk₀ (reference R))))
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ b.app (ofChain (ComposableArrows.mk₀ (reference R))))
    (𝟙 _)

lemma section_evaluation : sectionMap R ≫ OrdinaryBarEvaluation.evaluation R a b =
    UniverseLift.map.{u} (smallAction R a b) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  change SSet.yonedaEquiv (OrdinaryBarFirstAction.action R a b
    ((Functor.const (Fin (n.unop.len + 1))).obj (reference R))
    (SSet.yonedaEquiv.symm x.down)) = (smallAction R a b).app n x.down
  unfold OrdinaryBarFirstAction.action
  rw [NerveFirstChoice.constant, NerveFirstChoice.constant]
  change SSet.yonedaEquiv
    (MixedResolutionCenters.action C (OrdinaryBarCenters.center R (reference R))
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        a.app (ofChain (ComposableArrows.mk₀ (reference R))))
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        b.app (ofChain (ComposableArrows.mk₀ (reference R))))
      (SSet.yonedaEquiv.symm x.down)) = _
  have h := MixedResolutionCenters.action_parameter C (OrdinaryBarCenters.center R (reference R))
    (SSet.yonedaEquiv.symm x.down)
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ a.app (ofChain (ComposableArrows.mk₀ (reference R))))
    (SSet.stdSimplex.isTerminalObj₀.from _ ≫ b.app (ofChain (ComposableArrows.mk₀ (reference R))))
    (𝟙 ((OrdinaryBarEvaluation.raw (C := C)).obj (OrdinaryResolutionPairs.forgetFrames.obj R)))
  simp only [Category.comp_id] at h
  have hp : SSet.yonedaEquiv.symm x.down ≫ SSet.stdSimplex.isTerminalObj₀.from _ =
      SSet.stdSimplex.isTerminalObj₀.from _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← Category.assoc, hp, ← Category.assoc, hp] at h
  calc
    _ = SSet.yonedaEquiv (SSet.yonedaEquiv.symm x.down ≫ smallAction R a b) :=
      (congrArg SSet.yonedaEquiv h).symm
    _ = _ := by rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma smallAction_weakEquivalence : weakEquivalences SSet.{v} (smallAction R a b) :=
  MixedCenterActionWeakEquivalence.action_weakEquivalence C hcof hfib
    (OrdinaryBarCenters.center R (reference R))
    ((weakEquivalences C).id_mem _) ((weakEquivalences Cᵒᵖ).id_mem _) _ _ (𝟙 _)
    ((weakEquivalences SSet.{v}).id_mem _)

include hcof hfib in
lemma section_evaluation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (sectionMap R ≫ OrdinaryBarEvaluation.evaluation R a b)) := by
  rw [section_evaluation]
  exact (UniverseLift.weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib
    (smallAction R a b)).mp (smallAction_weakEquivalence R a b hcof hfib)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReference
