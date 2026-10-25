module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.TwistedEndDifferential
/-!
概要：各単体の安定値は元の実 bar の鎖自己写像を定める。
方針：theta が単体次数を下げることから、各列の閉性を一つの有限段階へ戻す。
規約：同じ theta の MC 仮定のみを使う。像の正規化性と冪等性は別の命題。
使われ方：完成した正規化作用素と変形 retract の構成。
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

include hMC in
lemma dgCoherentBarNormalizationProjectorGraded_twisted_closed :
    dgCoherentBarTwistedEndDifferential R D F 0
      (dgCoherentBarNormalizationProjectorGraded R D F) = 0 := by
  apply (dgCoherentBarHomEquiv R D F (dgCoherentBarGraded R D F) 1).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply, map_zero]
  have h := dgCoherentBarTwistedEndDifferential_restrict_congr R D F 0
    (dgCoherentBarNormalizationProjectorGraded R D F)
    (dgCoherentBarNormalizationStageGraded R D F (s.1 + 1)) s (fun t ht => by
      rw [dgCoherentBarNormalizationProjectorGraded_restrict]
      exact (dgCoherentBarNormalizationStageGraded_restrict_stable R D F t
        (Nat.lt_succ_self t.1) (Nat.add_le_add_right ht 1)).symm)
  change (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
    (dgCoherentBarGraded R D F)).f (0 + 1)
      (dgCoherentBarTwistedEndDifferential R D F 0
        (dgCoherentBarNormalizationProjectorGraded R D F)) = 0
  rw [h, dgCoherentBarNormalizationStageGraded_twisted_closed R D F hMC, map_zero]

def dgCoherentBarNormalizationEndomorphism :
    dgCoherentBarObject R D F hMC ⟶ dgCoherentBarObject R D F hMC :=
  moduleMorphismOfCycle R D
    (M := dgCoherentBarObject R D F hMC) (N := dgCoherentBarObject R D F hMC)
    (dgCoherentBarEndRebase R D F hMC 0
      (dgCoherentBarNormalizationProjectorGraded R D F)) (by
    change (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d 0 (0 + 1)
        (dgCoherentBarEndRebase R D F hMC 0
          (dgCoherentBarNormalizationProjectorGraded R D F)) = 0
    rw [dgCoherentBarEndRebase_d]
    change dgCoherentBarEndRebase R D F hMC 1
      (dgCoherentBarTwistedEndDifferential R D F 0
        (dgCoherentBarNormalizationProjectorGraded R D F)) = 0
    rw [dgCoherentBarNormalizationProjectorGraded_twisted_closed R D F hMC,
      dgCoherentBarEndRebase_zero])

lemma dgCoherentBarNormalizationEndomorphism_cycle :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarNormalizationEndomorphism R D F hMC))).val =
    dgCoherentBarEndRebase R D F hMC 0
      (dgCoherentBarNormalizationProjectorGraded R D F) :=
  moduleMorphismOfCycle_cycle R D _ _

end SerrePositivity.InfinityCategories
