module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.AccumulatedHomotopyEquation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StabilizedEndomorphism
/-!
概要：安定した正規化自己写像は同じ theta の実微分で恒等写像に鎖ホモトピックである。
方針：累積ホモトピーの有限段階の方程式を各単体の安定次数で適用する。
規約：全 dg 自然な Hom 要素を使い、評価ごとの存在証明で代用しない。
使われ方：正規化部分への因子化後の変形 retract と Hom の比較。
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
lemma dgCoherentBarNormalizationStableHomotopyGraded_twisted_d :
    dgCoherentBarTwistedEndDifferential R D F (-1)
      (dgCoherentBarNormalizationStableHomotopyGraded R D F) =
      dgCoherentBarNormalizationProjectorGraded R D F -
      (unitElement R
        (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val := by
  apply (dgCoherentBarHomEquiv R D F (dgCoherentBarGraded R D F) 0).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply, dgCoherentBarHomEquiv_apply, map_sub,
    dgCoherentBarNormalizationProjectorGraded_restrict]
  have h := dgCoherentBarTwistedEndDifferential_restrict_congr R D F (-1)
    (dgCoherentBarNormalizationStableHomotopyGraded R D F)
    (dgCoherentBarNormalizationAccumulatedHomotopyGraded R D F (s.1 + 1)) s
    (fun t ht => by
      rw [dgCoherentBarNormalizationStableHomotopyGraded_restrict]
      exact (dgCoherentBarNormalizationAccumulatedHomotopyGraded_restrict_stable R D F t
        (Nat.lt_succ_self t.1) (Nat.add_le_add_right ht 1)).symm)
  rw [dgCoherentBarNormalizationAccumulatedHomotopyGraded_twisted_d R D F hMC,
    map_sub] at h
  exact h

def dgCoherentBarNormalizationEndomorphismHomotopy :
    ModuleHomotopy R D (dgCoherentBarNormalizationEndomorphism R D F hMC) (𝟙 _) :=
  ⟨dgCoherentBarEndRebase R D F hMC (-1)
    (dgCoherentBarNormalizationStableHomotopyGraded R D F), by
    change (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d (-1) 0 _ = _
    rw [dgCoherentBarNormalizationEndomorphism_cycle]
    change (moduleHom R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC)).d (-1) (-1 + 1) _ =
      dgCoherentBarEndRebase R D F hMC 0
        (dgCoherentBarNormalizationProjectorGraded R D F) -
      (unitElement R (dgCoherentBarModule R D F hMC)).val
    rw [dgCoherentBarEndRebase_d]
    change dgCoherentBarEndRebase R D F hMC 0
      (dgCoherentBarTwistedEndDifferential R D F (-1)
        (dgCoherentBarNormalizationStableHomotopyGraded R D F)) = _
    rw [dgCoherentBarNormalizationStableHomotopyGraded_twisted_d R D F hMC,
      dgCoherentBarEndRebase_sub, dgCoherentBarEndRebase_unit]⟩

end SerrePositivity.InfinityCategories
