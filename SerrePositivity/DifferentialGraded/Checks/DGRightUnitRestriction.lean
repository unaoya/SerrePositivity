module
public import SerrePositivity.DifferentialGraded.Derived.RightUnitRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 右単位子・制限比較と任意K-flat解像度のモデル独立性の検査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section General
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

-- Cの局所Hom条件やFの本質的全射性は不要。前因子は任意の導来対象。
example (hD : localHomKFlat A D) (hF : HomQuasiIso F)
    (P : DerivedBimoduleCategory A B C) :
    (rightUnitRestrictionDerivedComparison A B C D F hD).app P =
      (derivedBimoduleRightUnitIso A B D hD).hom.app
        ((derivedBimoduleRestriction A B D B C (DGFunctor.id B) F).obj P) :=
  NatTrans.congr_app (rightUnitRestrictionDerivedComparison_eq A B C D F hD hF) P

variable (E : Type t) [DGCategory A E] [Small.{u} E]

-- 解像度は右相対K-flatであればよく、semifree性やHomのA-flat性を追加しない。
example (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q :=
  derivedMiddleRestrictionComparison_kFlat_eq_canonical A B C D E F hE Q R q hq P
end General

example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
    (D : Type z) [DGCategory (ZMod 2) D] [Small.{0} D]
    (F : DGFunctor (ZMod 2) D C) (hD : localHomKFlat (ZMod 2) D)
    (hF : HomQuasiIso F) :
    rightUnitRestrictionDerivedComparison (ZMod 2) B C D F hD =
      whiskerLeft (derivedBimoduleRestriction (ZMod 2) B D B C (DGFunctor.id B) F)
        (derivedBimoduleRightUnitIso (ZMod 2) B D hD).hom :=
  rightUnitRestrictionDerivedComparison_eq (ZMod 2) B C D F hD hF

#print axioms rightUnitRestriction_value
#print axioms rightUnitRestriction
#print axioms composeAfter_bimoduleCanonicalResolutionLift_fac
#print axioms derivedMiddleRestrictionComparison_kFlat_eq_canonical
#print axioms rightUnitRestriction_source_computation
#print axioms derivedRightUnitRestriction_model
#print axioms rightUnitRestrictionMiddleMap
#print axioms rightUnitRestrictionDerivedComparison
#print axioms rightUnitRestriction_source_identification
#print axioms rightUnitRestrictionMiddleMap_base_fac
#print axioms rightUnitRestriction_target_calculation
#print axioms rightUnitRestrictionDerivedComparison_base_fac
#print axioms rightUnitRestrictionDerivedComparison_eq
