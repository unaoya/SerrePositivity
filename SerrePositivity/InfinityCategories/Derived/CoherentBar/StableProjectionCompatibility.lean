module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StableHomotopyImage
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedDifferential
/-!
概要：安定正規化作用素は非退化因子への元の射影を変えない。
方針：正規化射影が theta と可換であることを用い、累積ホモトピーの微分の射影像を消す。
規約：同じ theta と全 prefix 項を保持する。
使われ方：正規化側の補正包含の分裂式。
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

lemma dgCoherentBarTwistedEndDifferential_normalizedProjection_eq_zero
    (z : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X (-1))
    (hz : (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f (-1) z = 0) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f 0
      (dgCoherentBarTwistedEndDifferential R D F (-1) z) = 0 := by
  have hd := ConcreteCategory.congr_hom
    ((eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).comm (-1) 0) z
  change (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).d (-1) 0
      ((eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
        (dgCoherentBarNormalizedProjection R D F)).f (-1) z) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f 0
      ((moduleHom R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d (-1) 0 z) at hd
  rw [hz, map_zero] at hd
  unfold dgCoherentBarTwistedEndDifferential
  simp only [show (-1 : ℤ) + 1 = 0 from rfl, Int.negOnePow_zero, one_smul]
  change (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
    (dgCoherentBarNormalizedProjection R D F)).f 0
    ((moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d (-1) 0 z +
      compose R (n := 0)
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) z rfl +
      compose R (n := 0)
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        z (dgCoherentBarTheta R D F) rfl) = 0
  rw [map_add, map_add, ← hd, zero_add, dgCoherentBarHom_postcompose_comp R D,
    ← dgCoherentBarNormalizedTheta_projection, ← moduleHomClosedInsertion R D,
    hz, DGNerve.compose_zero, zero_add, dgCoherentBarHom_postcompose_comp R D,
    hz, DGNerve.zero_compose]

lemma dgCoherentBarNormalizationProjectorGraded_normalizedProjection
    (hMC : dgCoherentBarMaurerCartan R D F) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f 0
      (dgCoherentBarNormalizationProjectorGraded R D F) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f 0
      (unitElement R
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val := by
  have h := dgCoherentBarTwistedEndDifferential_normalizedProjection_eq_zero R D F
    (dgCoherentBarNormalizationStableHomotopyGraded R D F)
    (dgCoherentBarNormalizationStableHomotopyGraded_normalizedProjection R D F)
  rw [dgCoherentBarNormalizationStableHomotopyGraded_twisted_d R D F hMC,
    map_sub] at h
  exact sub_eq_zero.mp h

end SerrePositivity.InfinityCategories
