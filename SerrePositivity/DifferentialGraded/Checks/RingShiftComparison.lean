module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 一対象Aの評価・主導来比較のshift coherenceの監査 -/
@[expose] public section
noncomputable section
universe u w
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : (complexToRingModule A).CommShift ℤ := inferInstance
example : NatTrans.CommShift (complexToRingModuleEvaluationIso A).hom ℤ := inferInstance
example (P : Complex A) (s : ℤ) :
    (complexToRingModule A).obj (P⟦s⟧) ≅ ((complexToRingModule A).obj P)⟦s⟧ :=
  (complexToRingModule A).commShiftIso s |>.app P

section
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
example : NatTrans.CommShift (complexToRingModuleDerivedEvaluationIso A).hom ℤ := inferInstance
example : (ringDerivedEquivalence A).CommShift ℤ := inferInstance
example : NatTrans.CommShift (ringComplexDerivedUnitNatIso A).hom ℤ := inferInstance
example (s t : ℤ) :
    (complexToRingModule A).commShiftIso (s + t) =
      Functor.CommShift.isoAdd ((complexToRingModule A).commShiftIso s)
        ((complexToRingModule A).commShiftIso t) :=
  (complexToRingModule A).commShiftIso_add s t
end

example : (complexToRingModule (ZMod 2)).CommShift ℤ := inferInstance

#print axioms complexToRingModuleCommShift
#print axioms complexToRingModuleEvaluationIsoCommShift
#print axioms complexToRingModuleDerivedEvaluationIsoCommShift
#print axioms ringDerivedEquivalenceShiftCompatible
#print axioms ringComplexDerivedUnitNatIso
#print axioms ringComplexDerivedUnitNatIsoCommShift
