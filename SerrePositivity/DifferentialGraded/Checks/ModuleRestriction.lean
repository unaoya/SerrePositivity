module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRestrictionKFlat
public import Mathlib.Data.ZMod.Basic

/-! # dg加群制限の全Hom自然性・分裂・余極限・相対K-flat帰着の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Limits Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]
  (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

example : PreservesColimitsOfShape ℕ (moduleRestriction A D E F) := inferInstance

example {M N P : ModuleCategory A E} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A E f g) :
    ModuleGradedSplit A D ((moduleRestriction A D E F).map f)
      ((moduleRestriction A D E F).map g) := s.restrict A D E F

example {M N : ModuleCategory A E} (f : M ⟶ N) (hf : moduleQuasiIso A E f) :
    moduleQuasiIso A D ((moduleRestriction A D E F).map f) :=
  moduleRestriction_quasiIso A D E F f hf

example (hfree : ∀ (x : E) (n : ℤ), moduleRelativeKFlat A D
    (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj (freeSphere A E x n))))
    {M : ModuleCategory A E} (hM : moduleSemifree A E M) :
    moduleRelativeKFlat A D
      (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) :=
  moduleSemifree_restriction_relativeKFlat A D E F hfree hM

example (M : ModuleCategory A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ) (c : E) :
    (BimoduleCategory.evaluation A D E c).obj
        ((rightModuleBimoduleEquivalence A D E).functor.obj M) ≅
      (tensorRightRestriction A D E c).obj M :=
  rightModuleBimoduleRightRestrictionIso A D E M c

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C]
    (M : ModuleCategory (ZMod 2) (DGTensorCategory (ZMod 2) Bᵒᵖ C)ᵒᵖ) (c : C) :
    (BimoduleCategory.evaluation (ZMod 2) B C c).obj
        ((rightModuleBimoduleEquivalence (ZMod 2) B C).functor.obj M) ≅
      (tensorRightRestriction (ZMod 2) B C c).obj M :=
  rightModuleBimoduleRightRestrictionIso (ZMod 2) B C M c

#print axioms restrictModule
#print axioms moduleRestriction_naturality
#print axioms moduleRestrictionMap
#print axioms moduleRestrictionMap_eval
#print axioms moduleRestriction
#print axioms moduleRestriction_map_eval
#print axioms moduleRestrictionEvaluationIso
#print axioms moduleRestriction_map_zero
#print axioms moduleRestriction_quasiIso
#print axioms ModuleGradedSplit.restrict
#print axioms moduleRestriction_comp_evaluation
#print axioms moduleRestrictionIsColimit
#print axioms moduleRestrictionPreservesColimitsOfShape
#print axioms moduleRestrictionColimitIso
#print axioms sphereFreePresentation_restriction_relativeKFlat
#print axioms ModuleSemifreeFiltration.restriction_relativeKFlat_stage
#print axioms ModuleSemifreeFiltration.restriction_relativeKFlat
#print axioms moduleSemifree_restriction_relativeKFlat
#print axioms tensorRightRestrictionInclusion
#print axioms tensorRightRestriction
#print axioms tensorRightRestrictionEvaluationIso
#print axioms rightModuleBimoduleRightRestrictionIso
#print axioms rightModuleBimodule_semifree_rightRelativeKFlat
#print axioms BimoduleSemifreeResolution.rightRelativeKFlat_of_cells
