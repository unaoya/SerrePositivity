module

public import SerrePositivity.KST.Spectra.SkeletalCoefficientExactness
public import SerrePositivity.KST.Spectra.TowerDifferentialCorrection

/-!
概要：cohomology の消滅による骨格の実際の fiber 微分の完全性。
方針：係数微分の原像を、セルの係数群同型の逆で fiber のホモトピー群へ戻す。
規約：完全性を仮定せず、通常の正規化 cohomology の消滅から構成する。
使われ方：Goerss–Jardine VIII §§1–2。塔の障害補正への具体的な入力。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 正規化 cohomology が零なら、実際の fiber 微分の cocycle に原像がある。 -/
theorem stageDifferential_exists_preimage_of_isZero
    (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (hH : IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of (positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2)))
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y (n + 1)).right (r + 1)
      (UnbasedPointedMapping.stageFiber K Y (n + 1)).basepoint)
    (hz : UnbasedPointedMapping.stageDifferential K Y (n + 1) r z = 1) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right (r + 2)
        (UnbasedPointedMapping.stageFiber K Y n).basepoint,
      UnbasedPointedMapping.stageDifferential K Y n (r + 1) c = z := by
  have hcoef : coefficientDifferential K Y (n + 1) r
      (stageFiberCoefficientEquiv K Y (n + 1) (r + 1) z) = 1 := by
    rw [stageFiberCoefficientEquiv_differential, hz, map_one]
  obtain ⟨c, hc⟩ := coefficientDifferential_exists_preimage_of_isZero K Y n r hH _ hcoef
  refine ⟨(stageFiberCoefficientEquiv K Y n (r + 2)).symm c, ?_⟩
  apply (stageFiberCoefficientEquiv K Y (n + 1) (r + 1)).injective
  rw [← stageFiberCoefficientEquiv_differential, MulEquiv.apply_symm_apply]
  exact hc

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
