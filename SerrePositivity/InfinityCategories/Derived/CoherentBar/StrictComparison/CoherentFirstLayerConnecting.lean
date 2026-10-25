module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerEvaluation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerConnectingRepresentative
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerHomologyMap

/-!
概要：実長完全列の一次微分と、閉じた一次層作用素のホモロジー射の一致。
方針：内部 cycle の持上げ境界の代表元公式を実層射影へ送る。
規約：元の theta の高次成分は射影による消滅として扱う。
使われ方：通常の非退化ホモロジー bar との微分比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarLayerCycleLift_boundary_eq_theta (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarLayerGraded R D G (n + 1)))
    (hz : ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).d
      q (q + 1) z = 0) :
    ((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).d q (q + 1)
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1)) z) =
    (((moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G)) x).f 1
        (dgCoherentBarNormalizedTheta R D G)).v q (q + 1) rfl
          ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1)) z)) := by
  let a := (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1)) z
  have hc := ConcreteCategory.congr_hom
    (((moduleEvaluation R D x).map (dgCoherentBarLayerInclusion R D G (n + 1))).comm
      q (q + 1)) z
  have h0 : ((moduleEvaluation R D x).obj (dgCoherentBarNormalizedGraded R D G)).d
      q (q + 1) a = 0 := by
    simpa only [ModuleCat.comp_apply, hz, map_zero] using! hc
  have hd := congrArg (fun f => f a)
    (dgCoherentBarNormalizedModule_d R D G (dgCoherentBarMaurerCartan_unconditional R D G)
      (Opposite.op x) q)
  change _ = ((moduleEvaluation R D x).obj (dgCoherentBarNormalizedGraded R D G)).d
    q (q + 1) a + _ at hd
  simpa only [h0, zero_add] using! hd

lemma dgCoherentBarLayerCycleBoundary_projection (x : D) (q : ℤ) (n : ℕ) :
    dgCoherentBarLayerCycleBoundary R D G x q n ≫
      (dgCoherentBarStageToLayer R D G x n).f (q + 1) =
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).iCycles q ≫
      (dgCoherentBarFirstLayerCochain R D G x n).v q (q + 1) rfl := by
  ext c
  let z := ((moduleEvaluation R D x).obj
    (dgCoherentBarLayerGraded R D G (n + 1))).iCycles q c
  change (moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarLayerProjection R D G n)
    (((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).d q (q + 1)
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1)) z)) =
    (dgCoherentBarFirstLayerCochain R D G x n).v q (q + 1) rfl z
  rw [dgCoherentBarLayerCycleLift_boundary_eq_theta R D G x q n z
    (ConcreteCategory.congr_hom
      (((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).iCycles_d
        q (q + 1)) c)]
  exact dgCoherentBarLayerFirstHom_eval R D G x q n z

lemma dgCoherentBarLayerConnecting_eq_firstHomology (x : D) (q : ℤ) (n : ℕ) :
    (dgCoherentBarLayerSequence_shortExact R D G x n).δ q (q + 1) (by rfl) ≫
      HomologicalComplex.homologyMap (dgCoherentBarStageToLayer R D G x n) (q + 1) =
    dgCoherentBarFirstLayerHomologyMap R D G x q n := by
  let L := (moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)
  let K := (moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))
  let b := dgCoherentBarLayerCycleBoundary R D G x q n
  let p := dgCoherentBarStageToLayer R D G x n
  let hnext : (ComplexShape.up ℤ).next (q + 1) = q + 2 := by
    apply ComplexShape.next_eq'; change (q + 1) + 1 = q + 2; omega
  have hc : (dgCoherentBarNormalizedStageComplex R D G x n).liftCycles b (q + 2) hnext
      (dgCoherentBarLayerCycleBoundary_closed R D G x q n) ≫
        HomologicalComplex.cyclesMap p (q + 1) =
    L.liftCycles (K.iCycles q ≫ (dgCoherentBarFirstLayerCochain R D G x n).v q (q + 1) rfl)
      (q + 2) hnext (dgDegreeOneCochain_cycles_closed R _
        (dgCoherentBarFirstLayerCochain_closed R D G x n) q) := by
    rw [← cancel_mono (L.iCycles (q + 1)), Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
    exact dgCoherentBarLayerCycleBoundary_projection R D G x q n
  rw [← cancel_epi (K.homologyπ q), ← Category.assoc,
    dgCoherentBarLayerConnecting_representative, Category.assoc,
    HomologicalComplex.homologyπ_naturality]
  change _ = K.homologyπ q ≫ dgDegreeOneHomologyMap R _ _ q
  rw [dgDegreeOneHomologyMap_representative, ← Category.assoc, hc]

end SerrePositivity.InfinityCategories
