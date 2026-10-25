module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarDifferential
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitDifferential
public import SerrePositivity.DifferentialGraded.Module.HomClosedInsertion
public import SerrePositivity.InfinityCategories.DGNerve.Residual

/-!
概要：bar の各元の単体から、シフトを除いた次数付き閉包含を与える。
方針：元の余積包含に実 shift の次数付き単位を合成し、次元の符号を掛ける。
規約：bar の微分を変更せず、MC 方程式も仮定しない。
使われ方：Bianchi 恒等式の最後の頂点への係数と θ の列との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarShiftedInclusion (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X (-(s.1 : ℤ)) :=
  (s.1 : ℤ).negOnePow •
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
      (Sigma.ι (dgCoherentBarFamily R D F) s)).f (-(s.1 : ℤ))
        (moduleShiftInElement R D (s.1 : ℤ) (dgCoherentBarSource R D F s))

lemma dgCoherentBarShiftedInclusion_d (s : dgCoherentBarIndex I) :
    (moduleHom R D (dgCoherentBarSource R D F s)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d
        (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1) (dgCoherentBarShiftedInclusion R D F s) = 0 := by
  have hd := ConcreteCategory.congr_hom
    ((eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
      (Sigma.ι (dgCoherentBarFamily R D F) s)).comm (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1))
    (moduleShiftInElement R D (s.1 : ℤ) (dgCoherentBarSource R D F s))
  change (moduleHom R D (dgCoherentBarSource R D F s)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d
      (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1)
      ((eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
        (Sigma.ι (dgCoherentBarFamily R D F) s)).f (-(s.1 : ℤ))
        (moduleShiftInElement R D (s.1 : ℤ) (dgCoherentBarSource R D F s))) =
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
      (Sigma.ι (dgCoherentBarFamily R D F) s)).f (-(s.1 : ℤ) + 1)
      ((moduleHom R D (dgCoherentBarSource R D F s)
        (shiftModule (s.1 : ℤ) (dgCoherentBarSource R D F s))).d
        (-(s.1 : ℤ)) (-(s.1 : ℤ) + 1)
        (moduleShiftInElement R D (s.1 : ℤ) (dgCoherentBarSource R D F s))) at hd
  rw [moduleShiftInElement_d R D (s.1 : ℤ) (dgCoherentBarSource R D F s), map_zero] at hd
  unfold dgCoherentBarShiftedInclusion
  simp only [Units.smul_def, map_zsmul]
  exact (congrArg (fun z => (s.1 : ℤ).negOnePow • z) hd).trans (smul_zero _)

lemma dgCoherentBarTheta_comp_shiftedInclusion (s : dgCoherentBarIndex I) :
    compose R (x := dgCoherentBarSource R D F s)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarTheta R D F) (dgCoherentBarShiftedInclusion R D F s) rfl =
    (s.1 : ℤ).negOnePow •
      compose R (x := dgCoherentBarSource R D F s)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarColumn R D F s)
        (moduleShiftInElement R D (s.1 : ℤ) (dgCoherentBarSource R D F s)) rfl := by
  unfold dgCoherentBarShiftedInclusion
  rw [compose_units_smul_right, moduleHomClosedInsertion R D
    (S := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D F s))
    (M := dgCoherentBarFamily R D F s) (N := dgCoherentBarGraded R D F)
    (P := dgCoherentBarGraded R D F), dgCoherentBarTheta_restrict R D F]

end SerrePositivity.InfinityCategories
