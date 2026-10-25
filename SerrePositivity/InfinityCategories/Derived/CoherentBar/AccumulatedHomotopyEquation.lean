module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.HomotopyStabilization
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.TwistedEndDifferential
/-!
概要：累積した次数マイナス一作用素の微分は有限段階と恒等の差になる。
方針：実 MC Hom の Leibniz 則で増分を計算し、有限段階の閉性を使う。
規約：元の theta の微分による等式を全 Hom 上で証明する。
使われ方：単体ごとに安定化した鎖ホモトピーの方程式。
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
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNormalizationIncrement_d (q : ℕ) :
    (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d (-1) 0
      (dgCoherentBarEndRebase R D F hMC (-1)
        (compose R (n := (-1))
          (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
          (dgCoherentBarNormalizationHomotopyGraded R D F q)
          (dgCoherentBarNormalizationStageGraded R D F q) rfl)) =
    dgCoherentBarEndRebase R D F hMC 0
      (compose R (n := 0)
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarNormalizationBoundaryGraded R D F q)
        (dgCoherentBarNormalizationStageGraded R D F q) rfl) := by
  have hp : (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d 0 1
      (dgCoherentBarEndRebase R D F hMC 0
        (dgCoherentBarNormalizationStageGraded R D F q)) = 0 := by
    rw [← dgCoherentBarNormalizationStage_cycle]
    exact (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarNormalizationStage R D F hMC q))).property
  have hh := dgCoherentBarNormalizationBoundary_cycle R D F hMC q
  rw [dgCoherentBarNormalizationBoundary, moduleMorphismOfCycle_cycle] at hh
  change (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d (-1) 0
      (dgCoherentBarEndRebase R D F hMC (-1)
        (dgCoherentBarNormalizationHomotopyGraded R D F q)) =
    dgCoherentBarEndRebase R D F hMC 0
      (dgCoherentBarNormalizationBoundaryGraded R D F q) at hh
  rw [← dgCoherentBarEndRebase_compose]
  have hd := differential_compose R
    (x := dgCoherentBarModule R D F hMC) (y := dgCoherentBarModule R D F hMC)
    (z := dgCoherentBarModule R D F hMC)
    (dgCoherentBarEndRebase R D F hMC (-1)
      (dgCoherentBarNormalizationHomotopyGraded R D F q))
    (dgCoherentBarEndRebase R D F hMC 0
      (dgCoherentBarNormalizationStageGraded R D F q))
    (show (0 : ℤ) + -1 = -1 from rfl)
  change (moduleHom R D (dgCoherentBarModule R D F hMC)
    (dgCoherentBarModule R D F hMC)).d (-1) 0 _ = _ at hd
  change (moduleHom R D (dgCoherentBarModule R D F hMC)
    (dgCoherentBarModule R D F hMC)).d (-1) 0 _ =
      compose R (n := 0)
        (x := dgCoherentBarModule R D F hMC) (y := dgCoherentBarModule R D F hMC)
        (z := dgCoherentBarModule R D F hMC)
        ((moduleHom R D (dgCoherentBarModule R D F hMC)
          (dgCoherentBarModule R D F hMC)).d (-1) 0
          (dgCoherentBarEndRebase R D F hMC (-1)
            (dgCoherentBarNormalizationHomotopyGraded R D F q)))
        (dgCoherentBarEndRebase R D F hMC 0
          (dgCoherentBarNormalizationStageGraded R D F q)) rfl +
      (-1 : ℤ).negOnePow • compose R (n := 0)
        (x := dgCoherentBarModule R D F hMC) (y := dgCoherentBarModule R D F hMC)
        (z := dgCoherentBarModule R D F hMC)
        (dgCoherentBarEndRebase R D F hMC (-1)
          (dgCoherentBarNormalizationHomotopyGraded R D F q))
        ((moduleHom R D (dgCoherentBarModule R D F hMC)
          (dgCoherentBarModule R D F hMC)).d 0 1
          (dgCoherentBarEndRebase R D F hMC 0
            (dgCoherentBarNormalizationStageGraded R D F q))) rfl at hd
  rw [hp, hh, DGNerve.compose_zero, smul_zero, add_zero] at hd
  simpa only [dgCoherentBarEndRebase_compose] using hd

lemma dgCoherentBarNormalizationAccumulatedHomotopy_d (q : ℕ) :
    (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d (-1) 0
      (dgCoherentBarEndRebase R D F hMC (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q)) =
    dgCoherentBarEndRebase R D F hMC 0
      (dgCoherentBarNormalizationStageGraded R D F q) -
      (unitElement R (dgCoherentBarModule R D F hMC)).val := by
  induction q with
  | zero => rw [dgCoherentBarNormalizationAccumulatedHomotopyGraded,
      dgCoherentBarEndRebase_zero, map_zero,
      dgCoherentBarNormalizationStageGraded, dgCoherentBarEndRebase_unit, sub_self]
  | succ q ih =>
    rw [dgCoherentBarNormalizationAccumulatedHomotopyGraded,
      dgCoherentBarEndRebase_add, map_add, ih, dgCoherentBarNormalizationIncrement_d,
      dgCoherentBarNormalizationStageGraded, DGNerve.compose_add_left, unit_compose,
      dgCoherentBarEndRebase_add]
    abel

include hMC in
lemma dgCoherentBarNormalizationAccumulatedHomotopyGraded_twisted_d (q : ℕ) :
    dgCoherentBarTwistedEndDifferential R D F (-1)
      (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q) =
      dgCoherentBarNormalizationStageGraded R D F q -
      (unitElement R
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val := by
  apply dgCoherentBarEndRebase_injective R D F hMC 0
  have h := dgCoherentBarEndRebase_d R D F hMC (-1)
    (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q)
  change (moduleHom R D (dgCoherentBarModule R D F hMC)
    (dgCoherentBarModule R D F hMC)).d (-1) 0
      (dgCoherentBarEndRebase R D F hMC (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q)) =
    dgCoherentBarEndRebase R D F hMC 0
      (dgCoherentBarTwistedEndDifferential R D F (-1)
        (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F q)) at h
  rw [← h, dgCoherentBarEndRebase_sub, dgCoherentBarEndRebase_unit]
  exact dgCoherentBarNormalizationAccumulatedHomotopy_d R D F hMC q

end SerrePositivity.InfinityCategories
