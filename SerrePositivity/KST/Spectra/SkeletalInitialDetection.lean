module

public import SerrePositivity.KST.Spectra.SkeletalMappingDetection
public import SerrePositivity.KST.Spectra.SkeletalFirstFiber
public import SerrePositivity.KST.Spectra.TowerInitialDetection

/-!
概要：正次数 cohomology の消滅により写像空間の高次群を零骨格で検出する。
方針：H¹ による最初の fiber の消滅と、高い段の fiber の完全性を組み合わせる。
規約：源の零単体は一つ。通常の cohomology の消滅を明示する。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の定数写像への帰着。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet Opposite HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) [Subsingleton (K _⦋0⦌)]
  (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (r : ℕ)
  (hfirst : IsZero ((NormalizedValueCochains.complex K
    (AddCommGrpCat.of (SkeletalCellAttachment.positiveAdditiveCoefficient Y 0 r))).homology 1))
  (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
    (AddCommGrpCat.of
      (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2)))

include hfirst hH in
/-- 正次数 cohomology 消滅の下で、整合族の初段での評価は単射。 -/
theorem compatibleGroup_stage_zero_injective_of_isZero :
    Function.Injective (fun a : PointedFibrationTower.compatibleGroup
      (fun n ↦ (tower K Y).obj (op n))
      (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) (r + 1) ↦ a.val 0) := by
  let X := fun n ↦ (tower K Y).obj (op n)
  let p := fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op
  let : ∀ n, Fibration (p n).right := fun n ↦ tower_map_fibration K Y _
  apply PointedFibrationTower.compatibleGroup_stage_zero_injective X p r
  · intro n z hz
    exact SkeletalCellAttachment.stageDifferential_exists_preimage_of_isZero K Y n r (hH n) z hz
  · intro z hz
    exact SkeletalCellAttachment.first_stage_cocycle_eq_one K Y r hfirst z hz

include hfirst hH in
/-- 正次数 cohomology 消滅の下で、通常の写像空間の高次群の零骨格への制限は単射。 -/
theorem stageZeroGroupMap_injective_of_isZero :
    Function.Injective (pointedGroupMap (X := obj K Y) (r + 1) ((cone K Y).π.app (op 0))) := by
  intro a b h
  apply (mappingGroupEquivOfCohomologyIsZero K Y r hH).injective
  apply compatibleGroup_stage_zero_injective_of_isZero K Y r hfirst hH
  change (mappingGroupEquivOfCohomologyIsZero K Y r hH a).val 0 =
    (mappingGroupEquivOfCohomologyIsZero K Y r hH b).val 0
  rw [mappingGroupEquivOfCohomologyIsZero_apply, mappingGroupEquivOfCohomologyIsZero_apply]
  exact h

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
