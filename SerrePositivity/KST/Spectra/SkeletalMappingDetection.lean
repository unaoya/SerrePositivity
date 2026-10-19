module

public import SerrePositivity.KST.Spectra.SkeletalMappingGroupComparison
public import SerrePositivity.KST.Spectra.TowerCompatibleDetection

/-!
概要：高次 cohomology の消滅の下で、写像空間の群を一骨格への制限から検出する。
方針：fiber 微分の完全性による整合族の検出を、収束の比較同型と合成する。
規約：最初の fiber に必要な一次 cohomology はまだ使わない。
使われ方：Goerss–Jardine VIII §§1–2。有理 Shapiro の最初の fiber への帰着。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet Opposite HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]

/-- cohomology の消滅により、整合族の段一での評価は単射。 -/
theorem compatibleGroup_stage_one_injective_of_isZero (r : ℕ)
    (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of
        (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2))) :
    Function.Injective (fun a : PointedFibrationTower.compatibleGroup
      (fun n ↦ (tower K Y).obj (op n))
      (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) (r + 1) ↦ a.val 1) := by
  let X := fun n ↦ (tower K Y).obj (op n)
  let p := fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op
  let : ∀ n, Fibration (p n).right := fun n ↦ tower_map_fibration K Y _
  apply PointedFibrationTower.compatibleGroup_stage_one_injective X p r
  intro n z hz
  exact SkeletalCellAttachment.stageDifferential_exists_preimage_of_isZero K Y n r (hH n) z hz

/-- cohomology の消滅により、通常の写像空間の高次群の一骨格への制限は単射。 -/
theorem stageOneGroupMap_injective_of_isZero (r : ℕ)
    (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of
        (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2))) :
    Function.Injective (pointedGroupMap (X := obj K Y) (r + 1) ((cone K Y).π.app (op 1))) := by
  intro a b h
  apply (mappingGroupEquivOfCohomologyIsZero K Y r hH).injective
  apply compatibleGroup_stage_one_injective_of_isZero K Y r hH
  change (mappingGroupEquivOfCohomologyIsZero K Y r hH a).val 1 =
    (mappingGroupEquivOfCohomologyIsZero K Y r hH b).val 1
  rw [mappingGroupEquivOfCohomologyIsZero_apply, mappingGroupEquivOfCohomologyIsZero_apply]
  exact h

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
