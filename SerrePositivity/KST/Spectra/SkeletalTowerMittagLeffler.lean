module

public import SerrePositivity.KST.Spectra.SkeletalFiberExactness
public import SerrePositivity.KST.Spectra.TowerTwoStepRanges

/-!
概要：正規化 cohomology の消滅から実際の骨格の塔の像の安定化を導く。
方針：fiber 微分の完全性で射影を保つ持ち上げを作り、二段の像の一致を反復する。
規約：ここでは次の次数の群の Mittag–Leffler 条件と極限との比較までを述べる。
使われ方：Goerss–Jardine VIII §§1–2。有理自明作用の写像空間の塔の収束。
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

local instance step_fibration (n : ℕ) :
    Fibration ((tower K Y).map (homOfLE (Nat.le_succ n)).op).right :=
  tower_map_fibration K Y _

/-- 正規化 cohomology の消滅で、前段の射影を保ちながら次段に持ち上げる。 -/
theorem stage_exists_lift_preserving_projection (n r : ℕ)
    (hH : IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of
        (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2)))
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((tower K Y).obj (op (n + 1))).right (r + 2)
      ((tower K Y).obj (op (n + 1))).basepoint) :
    ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((tower K Y).obj (op (n + 2))).right (r + 2)
        ((tower K Y).obj (op (n + 2))).basepoint,
      pointedGroupMap (r + 2) ((tower K Y).map (homOfLE (Nat.le_succ n)).op)
        (pointedGroupMap (r + 2) ((tower K Y).map (homOfLE (Nat.le_succ (n + 1))).op) b) =
      pointedGroupMap (r + 2) ((tower K Y).map (homOfLE (Nat.le_succ n)).op) a := by
  let X := fun m ↦ (tower K Y).obj (op m)
  let p := fun m ↦ (tower K Y).map (homOfLE (Nat.le_succ m)).op
  let : ∀ m, Fibration (p m).right := fun m ↦ tower_map_fibration K Y _
  apply PointedFibrationTower.exists_lift_preserving_projection X p n r
  intro z hz
  exact SkeletalCellAttachment.stageDifferential_exists_preimage_of_isZero K Y n r hH z hz

/-- 正次数 cohomology の消滅から骨格の塔の高次群の像の安定化を得る。 -/
theorem groupTower_isMittagLeffler_of_isZero (r : ℕ)
    (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of
        (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((tower K Y).obj (op n)).right (r + 2)
        ((tower K Y).obj (op n)).basepoint)
      (fun n ↦ pointedGroupMap (r + 2) ((tower K Y).map (homOfLE (Nat.le_succ n)).op)) :=
  TowerLimOne.isMittagLeffler_of_two_step_lifting _ _
    (fun n a ↦ stage_exists_lift_preserving_projection K Y n r (hH n) a)

/-- cohomology の消滅による骨格の塔の極限のホモトピー群の比較同型。 -/
def limitGroupEquivOfCohomologyIsZero (r : ℕ)
    (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of
        (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ ((tower K Y).obj (op n)).right)
      (fun n ↦ ((tower K Y).map (homOfLE (Nat.le_succ n)).op).right)) (r + 1)
      (PointedFibrationTower.limitBasepoint (fun n ↦ (tower K Y).obj (op n))
        (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op)) ≃*
      PointedFibrationTower.compatibleGroup (fun n ↦ (tower K Y).obj (op n))
        (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) (r + 1) := by
  let X := fun n ↦ (tower K Y).obj (op n)
  let p := fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op
  let : ∀ n, Fibration (p n).right := fun n ↦ tower_map_fibration K Y _
  exact PointedFibrationTower.limitGroupEquivOfMittagLeffler X p (r + 1)
    (groupTower_isMittagLeffler_of_isZero K Y r hH)

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
