module
public import SerrePositivity.DifferentialGraded.Complexes.ShiftRepresentation
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitDifferential
public import SerrePositivity.DifferentialGraded.Functor.ClosedComplex
public import SerrePositivity.DifferentialGraded.Bimodule.Tensor

/-! # 反変複体値dg関手による加群shiftの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D)ᵒᵖ (Complex A))

def moduleShiftOppImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (Opposite.op (shiftModule s M))) (F.obj (Opposite.op M)) (-s) :=
  (F.map (Opposite.op (shiftModule s M)) (Opposite.op M)).f (-s) (moduleShiftInElement A D s M)

def moduleShiftOppImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (Opposite.op M)) (F.obj (Opposite.op (shiftModule s M))) s :=
  (s * s).negOnePow •
    (F.map (Opposite.op M) (Opposite.op (shiftModule s M))).f s (moduleShiftOutElement A D s M)

lemma moduleShiftOppImageOut_d (s : ℤ) (M : RightModule A D) :
    δ (-s) (-s + 1) (moduleShiftOppImageOut A D F s M) = 0 := by
  have h := F.map_d_cochain A
    (x := Opposite.op (shiftModule s M)) (y := Opposite.op M) (moduleShiftInElement A D s M) (q := -s + 1)
  have hz : (F.map (Opposite.op (shiftModule s M)) (Opposite.op M)).f (-s + 1)
      ((moduleHom A D M (shiftModule s M)).d (-s) (-s + 1)
        (moduleShiftInElement A D s M)) = 0 := by
    rw [moduleShiftInElement_d, map_zero]
  exact h.symm.trans hz

lemma moduleShiftOppImageOutIn (s : ℤ) (M : RightModule A D) :
    (moduleShiftOppImageOut A D F s M).comp (moduleShiftOppImageIn A D F s M)
        (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj (Opposite.op (shiftModule s M)))) := by
  have hs := opposite_compose A (RightModule A D)
    (Opposite.op (shiftModule s M)) (Opposite.op M) (Opposite.op (shiftModule s M)) (-s) s 0 (neg_add_cancel s)
    (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M)
  rw [moduleShiftOutIn] at hs
  simp only [neg_mul, Int.negOnePow_neg] at hs
  have h := congrArg (fun z => (F.map (Opposite.op (shiftModule s M))
    (Opposite.op (shiftModule s M))).f 0 z) hs
  rw [map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change (moduleShiftOppImageOut A D F s M).comp
      ((F.map (Opposite.op M) (Opposite.op (shiftModule s M))).f s (moduleShiftOutElement A D s M))
        (neg_add_cancel s) =
    (s * s).negOnePow • (F.map (Opposite.op (shiftModule s M)) (Opposite.op (shiftModule s M))).f 0
      (unitElement A (Opposite.op (shiftModule s M))).val at h
  rw [map_unitElement, Bimodule.complex_unitElement] at h
  rw [moduleShiftOppImageIn, Cochain.comp_units_smul, h, smul_smul,
    Int.units_mul_self, one_smul]

lemma moduleShiftOppImageInOut (s : ℤ) (M : RightModule A D) :
    (moduleShiftOppImageIn A D F s M).comp (moduleShiftOppImageOut A D F s M)
        (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (Opposite.op M))) := by
  have hs := opposite_compose A (RightModule A D)
    (Opposite.op M) (Opposite.op (shiftModule s M)) (Opposite.op M) s (-s) 0 (add_neg_cancel s)
    (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M)
  rw [moduleShiftInOut] at hs
  simp only [mul_neg, Int.negOnePow_neg] at hs
  have h := congrArg (fun z => (F.map (Opposite.op M) (Opposite.op M)).f 0 z) hs
  rw [map_compose_cochain] at h
  simp only [Units.smul_def, map_zsmul] at h
  change ((F.map (Opposite.op M) (Opposite.op (shiftModule s M))).f s (moduleShiftOutElement A D s M)).comp
      (moduleShiftOppImageOut A D F s M) (add_neg_cancel s) =
    (s * s).negOnePow • (F.map (Opposite.op M) (Opposite.op M)).f 0 (unitElement A (Opposite.op M)).val at h
  rw [map_unitElement, Bimodule.complex_unitElement] at h
  rw [moduleShiftOppImageIn, Cochain.units_smul_comp, h, smul_smul,
    Int.units_mul_self, one_smul]

/-- 反変dg関手は加群のshiftを符号反転した通常shiftへ送る。 -/
def moduleShiftOppImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (Opposite.op (shiftModule s M)) ≅ (F.obj (Opposite.op M))⟦-s⟧ :=
  complexShiftIsoOfSumZero A (moduleShiftOppImageOut A D F s M)
    (moduleShiftOppImageOut_d A D F s M) (moduleShiftOppImageIn A D F s M)
    (neg_add_cancel s) (moduleShiftOppImageOutIn A D F s M) (moduleShiftOppImageInOut A D F s M)

end SerrePositivity.DifferentialGraded.DGFunctor
