module

public import SerrePositivity.KST.Spectra.SkeletalMappingLimitIso
public import SerrePositivity.KST.Spectra.SkeletalTowerMittagLeffler

/-!
概要：通常の写像空間のホモトピー群と骨格各段の群の逆極限の比較。
方針：基点を保つ具体的な極限同型を合成し、各座標が骨格への制限と一致することを示す。
規約：比較の全射性は全正次数。同型には次の群の cohomology 消滅を使う。
使われ方：Goerss–Jardine VIII §§1–2。有理 Shapiro の通常の写像空間への接続。
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

local instance comparison_step_fibration (n : ℕ) :
    Fibration ((tower K Y).map (homOfLE (Nat.le_succ n)).op).right :=
  tower_map_fibration K Y _

/-- 通常の写像空間から骨格各段の群の逆極限への比較準同型。 -/
def groupComparison (r : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj K Y).right r (obj K Y).basepoint →*
    PointedFibrationTower.compatibleGroup (fun n ↦ (tower K Y).obj (op n))
      (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) r :=
  (PointedFibrationTower.limitGroupComparison (fun n ↦ (tower K Y).obj (op n))
    (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) r).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (skeletalLimitIso K Y).hom (skeletalLimitIso_basepoint K Y))

/-- 比較の各座標は元の写像空間から骨格への制限。 -/
lemma groupComparison_apply (r n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj K Y).right r (obj K Y).basepoint) :
    (groupComparison K Y r a).val n =
      pointedGroupMap (X := obj K Y) r ((cone K Y).π.app (op n)) a := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
  apply RelativeMorphism.ext
  change (s.map ≫ (skeletalLimitIso K Y).hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ n = s.map ≫ ((cone K Y).π.app (op n)).right
  rw [Category.assoc, skeletalLimitIso_hom_projection]

/-- 全正次数で、整合する骨格の類は通常の写像空間の類で実現できる。 -/
theorem groupComparison_surjective (r : ℕ) : Function.Surjective (groupComparison K Y r) :=
  (PointedFibrationTower.limitGroupComparison_surjective (fun n ↦ (tower K Y).obj (op n))
    (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) r).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r (skeletalLimitIso K Y)
        (skeletalLimitIso_basepoint K Y)).surjective

/-- cohomology 消滅の下で通常の写像空間の高次群を骨格各段の群の逆極限で表す。 -/
def mappingGroupEquivOfCohomologyIsZero (r : ℕ)
    (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of
        (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj K Y).right (r + 1) (obj K Y).basepoint ≃*
      PointedFibrationTower.compatibleGroup (fun n ↦ (tower K Y).obj (op n))
        (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) (r + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (r + 1) (skeletalLimitIso K Y)
    (skeletalLimitIso_basepoint K Y)).trans (limitGroupEquivOfCohomologyIsZero K Y r hH)

/-- cohomology 消滅の比較同型も各骨格への元の制限を計算する。 -/
lemma mappingGroupEquivOfCohomologyIsZero_apply (r : ℕ)
    (hH : ∀ n, IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of
        (SkeletalCellAttachment.positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2)))
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj K Y).right (r + 1) (obj K Y).basepoint) (n : ℕ) :
    (mappingGroupEquivOfCohomologyIsZero K Y r hH a).val n =
      pointedGroupMap (X := obj K Y) (r + 1) ((cone K Y).π.app (op n)) a :=
  groupComparison_apply K Y (r + 1) n a

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
