module
public import SerrePositivity.DifferentialGraded.Complexes.ConeShift
public import SerrePositivity.DifferentialGraded.Module.ShiftElements
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.DifferentialGraded.Module.ConeLift
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc

/-! # cone shift比較射の全dg自然な入力 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeShiftFirst (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M))).X 1 :=
  (moduleShiftHom A D s _ _).f 1 (moduleConeFstElement A D f)

def moduleConeShiftSecond (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N))).X 0 :=
  (moduleShiftHom A D s _ _).f 0 (moduleConeSndElement A D f)

def moduleConeShiftLeftInput (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).X (-1) :=
  (moduleShiftHom A D s _ _).f (-1) (moduleConeInlElement A D f)

lemma moduleConeShiftFirst_π (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M)) x).f 1 (moduleConeShiftFirst A D s f) =
        s.negOnePow • (mappingCone.fst ((moduleEvaluation A D x).map f)).val.shift s := by
  have h := moduleShiftHomElement_π A D s 1 (moduleConeFstElement A D f) x
  rw [moduleConeFstElement_π, mul_one] at h
  exact h

lemma moduleConeShiftSecond_π (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N)) x).f 0 (moduleConeShiftSecond A D s f) =
        (mappingCone.snd ((moduleEvaluation A D x).map f)).shift s := by
  have h := moduleShiftHomElement_π A D s 0 (moduleConeSndElement A D f) x
  rw [moduleConeSndElement_π, mul_zero, Int.negOnePow_zero, one_smul] at h
  exact h

lemma moduleConeShiftLeftInput_π (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f))) x).f (-1)
        (moduleConeShiftLeftInput A D s f) =
      s.negOnePow • (mappingCone.inl ((moduleEvaluation A D x).map f)).shift s := by
  have h := moduleShiftHomElement_π A D s (-1) (moduleConeInlElement A D f) x
  rw [moduleConeInlElement_π, mul_neg_one, Int.negOnePow_neg] at h
  exact h

lemma moduleConeShiftFirst_closed (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) M))).d 1 2
        (moduleConeShiftFirst A D s f) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeShiftFirst_π, map_zero]
  exact Cocycle.δ_eq_zero
    (s.negOnePow • (mappingCone.fst ((moduleEvaluation A D x).map f)).shift s) 2

lemma moduleConeShiftInputs_cycle (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
      (shiftModule s (ForgetEnrichment.to (Complex A) N))).d 0 1 (moduleConeShiftSecond A D s f) +
      (show (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))
        (shiftModule s (ForgetEnrichment.to (Complex A) N))).X 1 from
        (eHomWhiskerLeft (Complex A) (moduleShiftObj A D s (moduleCone A D f))
          (moduleShiftMap A D s f)).f 1 (moduleConeShiftFirst A D s f)) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomElement_d_π, moduleConeShiftSecond_π, map_zero]
  have hp := moduleHomWhiskerLeft_apply_π A D
    (T := moduleShiftObj A D s (moduleCone A D f)) (moduleShiftMap A D s f) 1
    (moduleConeShiftFirst A D s f) x
  have hfirst := moduleConeShiftFirst_π A D s f x
  have hp' := hp.trans (congrArg
    (fun z => z.comp (Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftMap A D s f)))
      (add_zero 1)) hfirst)
  exact (congrArg
    (fun z : Cochain ((mappingCone ((moduleEvaluation A D x).map f))⟦s⟧)
      (((moduleEvaluation A D x).obj N)⟦s⟧) 1 =>
        δ 0 1 ((mappingCone.snd ((moduleEvaluation A D x).map f)).shift s) + z) hp').trans
    (complexConeShift_lift_condition _ _ _ (moduleShiftMap_eval A D s f x))

lemma moduleConeShiftLeftInput_d (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (shiftModule s (ForgetEnrichment.to (Complex A) M))
      (shiftModule s (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
        (moduleConeShiftLeftInput A D s f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleShiftMap A D s f ≫ moduleShiftMap A D s (moduleConeInr A D f)))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeShiftLeftInput_π]
  have he := moduleEvaluation_cochain A D x
    (moduleShiftMap A D s f ≫ moduleShiftMap A D s (moduleConeInr A D f))
  rw [CategoryTheory.Functor.map_comp, moduleShiftMap_eval A D s (moduleConeInr A D f) x,
    moduleConeInr_eval A D f x] at he
  exact (complexConeShift_desc_condition _ _ _ (moduleShiftMap_eval A D s f x)).trans he

end SerrePositivity.DifferentialGraded
