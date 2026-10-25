module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CycleAlgebra
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.GradedStabilization
/-!
概要：有限段階の graded 作用素は同じ theta の実 bar 上の鎖写像に一致する。
方針：閉零要素の加法・合成と MC 微分変更下での graded 代数の比較を反復する。
規約：MC 方程式は元の公開型の仮定引数に保つ。
使われ方：単体ごとの安定値に対する実微分の閉性。
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

lemma dgCoherentBarNormalizationStage_cycle (q : ℕ) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarNormalizationStage R D F hMC q))).val =
      dgCoherentBarEndRebase R D F hMC 0
        (dgCoherentBarNormalizationStageGraded R D F q) := by
  induction q with
  | zero => exact (dgCoherentBarEndRebase_unit R D F hMC).symm
  | succ q ih =>
    rw [dgCoherentBarNormalizationStage, dgCoherentBarCycle_comp R D,
      dgCoherentBarCycle_add R D, ih, dgCoherentBarNormalizationBoundary_cycle]
    change compose R (x := dgCoherentBarModule R D F hMC)
      (y := dgCoherentBarModule R D F hMC) (z := dgCoherentBarModule R D F hMC)
      ((unitElement R (dgCoherentBarModule R D F hMC)).val +
        dgCoherentBarEndRebase R D F hMC 0
          (dgCoherentBarNormalizationBoundaryGraded R D F q))
      (dgCoherentBarEndRebase R D F hMC 0
        (dgCoherentBarNormalizationStageGraded R D F q)) rfl = _
    rw [← dgCoherentBarEndRebase_unit R D F hMC,
      ← dgCoherentBarEndRebase_add, dgCoherentBarEndRebase_compose]
    rfl

end SerrePositivity.InfinityCategories
