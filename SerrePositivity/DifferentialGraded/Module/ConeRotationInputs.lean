module
public import SerrePositivity.DifferentialGraded.Module.LeftShiftElements
public import SerrePositivity.DifferentialGraded.Module.ConeLift
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence

/-! # cone三角形の回転比較射の入力と閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeRotationFirst {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N)).X 1 :=
  -moduleHomLeftShiftElement A D 1 (show (0 : ℤ) + 1 = 1 by omega)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val

def moduleConeRotationSecond {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 0 :=
  -moduleHomLeftShiftElement A D 1 (show (-1 : ℤ) + 1 = 0 by omega)
    (moduleConeInlElement A D f)

lemma moduleConeRotationFirst_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N) x).f 1 (moduleConeRotationFirst A D f) =
      -(Cochain.ofHom ((moduleEvaluation A D x).map f)).leftShift 1 1 (zero_add 1) := by
  unfold moduleConeRotationFirst
  rw [map_neg]
  have h₁ := moduleHomLeftShiftElement_π A D 1
    (show (0 : ℤ) + 1 = 1 by omega)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val x
  have h₂ := congrArg (fun c => c.leftShift 1 1 (zero_add 1))
    (moduleEvaluation_cochain A D x f).symm
  exact congrArg (fun c => -c) (h₁.trans h₂)

lemma moduleConeRotationSecond_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0
        (moduleConeRotationSecond A D f) =
      -(mappingCone.inl ((moduleEvaluation A D x).map f)).leftShift 1 0 (neg_add_cancel 1) := by
  unfold moduleConeRotationSecond
  rw [map_neg]
  have h₁ := moduleHomLeftShiftElement_π A D 1
    (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f) x
  have h₂ := congrArg (fun c => c.leftShift 1 0 (neg_add_cancel 1))
    (moduleConeInlElement_π A D f x)
  exact congrArg (fun c => -c) (h₁.trans h₂)

lemma moduleConeRotationFirst_closed {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) N)).d 1 2 (moduleConeRotationFirst A D f) = 0 := by
  let z := cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)
  have hd := moduleHomLeftShiftElement_d A D 1
    (M := ForgetEnrichment.to (Complex A) M) (N := ForgetEnrichment.to (Complex A) N)
    (show (0 : ℤ) + 1 = 1 by omega) (show (1 : ℤ) + 1 = 2 by omega) z.val
  have hz : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)).d 0 1 z.val = 0 := z.property
  rw [hz, moduleHomLeftShiftElement_zero, smul_zero] at hd
  unfold moduleConeRotationFirst
  rw [map_neg]
  exact (congrArg (fun a => -a) hd).trans neg_zero

lemma moduleConeRotationInputs_cycle {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d 0 1
        (moduleConeRotationSecond A D f) +
      (show (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleShiftObj A D 1 M))
        (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 1 from
        (eHomWhiskerLeft (Complex A) (moduleShiftObj A D 1 M) (moduleConeInr A D f)).f 1
          (moduleConeRotationFirst A D f)) = 0 := by
  let Z := moduleHom A D (shiftModule 1 (ForgetEnrichment.to (Complex A) M))
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))
  let r : moduleHom A D (shiftModule 1 (ForgetEnrichment.to (Complex A) M))
      (ForgetEnrichment.to (Complex A) N) ⟶ Z :=
    eHomWhiskerLeft (Complex A) (moduleShiftObj A D 1 M) (moduleConeInr A D f)
  let z := (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
  have hd := moduleHomLeftShiftElement_d A D 1
    (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (show (-1 : ℤ) + 1 = 0 by omega) (show (0 : ℤ) + 1 = 1 by omega)
    (moduleConeInlElement A D f)
  rw [moduleConeInlElement_d] at hd
  have hp := moduleHomLeftShiftElement_postcompose A D 1
    (show (0 : ℤ) + 1 = 1 by omega) z (moduleConeInr A D f)
  have hc := moduleHomCycle_postcompose A D f (moduleConeInr A D f)
  have hp' := (congrArg (moduleHomLeftShiftElement A D 1
    (show (0 : ℤ) + 1 = 1 by omega)) hc).symm.trans hp
  have hs : Z.d 0 1 (moduleHomLeftShiftElement A D 1
      (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f)) =
      -(r.f 1 (moduleHomLeftShiftElement A D 1
        (show (0 : ℤ) + 1 = 1 by omega) z)) := by
    have hd' := hd.trans (congrArg ((1 : ℤ).negOnePow • ·) hp')
    change Z.d 0 1 (moduleHomLeftShiftElement A D 1
      (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f)) =
        (1 : ℤ).negOnePow • (r.f 1
          (moduleHomLeftShiftElement A D 1 (show (0 : ℤ) + 1 = 1 by omega) z)) at hd'
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul] at hd'
    exact hd'
  change Z.d 0 1 (-moduleHomLeftShiftElement A D 1
    (show (-1 : ℤ) + 1 = 0 by omega) (moduleConeInlElement A D f)) +
      r.f 1 (-moduleHomLeftShiftElement A D 1 (show (0 : ℤ) + 1 = 1 by omega) z) = 0
  rw [map_neg, map_neg, hs, neg_neg, add_neg_cancel]

/-- M[1]からcone(inr f)への回転比較の順方向。 -/
def moduleConeRotationHom {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleShiftObj A D 1 M ⟶ moduleCone A D (moduleConeInr A D f) :=
  moduleConeLiftOfCycle A D (moduleConeInr A D f)
    (moduleConeRotationFirst A D f) (moduleConeRotationSecond A D f)
    (moduleConeRotationFirst_closed A D f) (moduleConeRotationInputs_cycle A D f)

end SerrePositivity.DifferentialGraded
