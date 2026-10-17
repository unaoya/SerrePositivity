module
public import SerrePositivity.DifferentialGraded.Resolution.Restriction
public import SerrePositivity.DifferentialGraded.Derived.RestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # dg圏変更の導来制限・両側bimodule評価・解像度比較の監査 -/
@[expose] public section
noncomputable section
universe u v w z t v' w'
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]

-- 対象宇宙を独立にし、HomのK-flat性・有界性を要求しない。
example (F : DGFunctor A B D) (G : DGFunctor A C E) (b : B) (c : C) :
    bimoduleRestriction A B C D E F G ⋙ BimoduleCategory.valueEvaluation A B C b c ≅
      BimoduleCategory.valueEvaluation A D E (F.obj b) (G.obj c) :=
  bimoduleRestrictionEvaluationIso A B C D E F G b c

example (F : DGFunctor A Bᵒᵖ Cᵒᵖ) (G : DGFunctor A Cᵒᵖ Dᵒᵖ) :
    moduleDerivedRestriction A C D G ⋙ moduleDerivedRestriction A B C F ≅
      moduleDerivedRestriction A B D (F.comp G) :=
  moduleDerivedRestrictionCompIso A B C D F G

example (P : KFlatDGResolution.{u, v, v'} A B) (Q : KFlatDGResolution.{u, w, w'} A C) :
    ResolutionBimodule.DerivedCategory A P Q ⥤
      DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  ResolutionBimodule.comparisonLeft A P Q

example (P : KFlatDGResolution.{u, v, v'} A B) (Q : KFlatDGResolution.{u, w, w'} A C) :
    ResolutionBimodule.DerivedCategory A (KFlatDGResolution.canonical A B)
      (KFlatDGResolution.canonical A C) ⥤
      DerivedBimoduleCategory A P.ComparisonSource Q.ComparisonSource :=
  ResolutionBimodule.comparisonRight A P Q

example (X : Type v) (Y : Type w) [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [Small.{0} X] [Small.{0} Y] (F : DGFunctor (ZMod 2) X Y) :
    DerivedModuleCategory (ZMod 2) Y ⥤ DerivedModuleCategory (ZMod 2) X :=
  dgDerivedRestriction (ZMod 2) X Y F

namespace SerrePositivity.DifferentialGraded
#print axioms moduleDerivedRestriction
#print axioms moduleDerivedRestriction_fac
#print axioms dgDerivedRestriction
#print axioms dgDerivedRestriction_fac
#print axioms moduleRestrictionIdObjIso
#print axioms moduleRestrictionIdIso
#print axioms moduleRestrictionCompObjIso
#print axioms moduleRestrictionCompIso
#print axioms moduleDerivedRestriction_lifting
#print axioms moduleDerivedRestrictionIdIso
#print axioms moduleDerivedRestrictionComp_fac
#print axioms moduleDerivedRestrictionComp_lifting
#print axioms moduleDerivedRestrictionCompIso
#print axioms moduleDerivedRestrictionCompIso_hom_app
#print axioms DGFunctor.tensor
#print axioms bimoduleRestrictionIndex
#print axioms bimoduleRestriction
#print axioms bimoduleRestriction_quasiIso
#print axioms derivedBimoduleRestriction
#print axioms derivedBimoduleRestriction_fac
#print axioms bimoduleRightModuleEvaluationIso
#print axioms bimoduleRestrictionEvaluationIso
#print axioms ResolutionBimodule.restriction
#print axioms ResolutionBimodule.comparisonLeft
#print axioms ResolutionBimodule.comparisonRight
end SerrePositivity.DifferentialGraded
