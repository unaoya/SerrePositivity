module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FibrationTowerLimitCone
public import SerrePositivity.KST.Spectra.PointedSkeletalMappingTower
public import SerrePositivity.KST.Spectra.TowerHomotopyComparison

/-!
概要：通常の写像空間と、骨格の塔の具体的な整合族の極限の同型。
方針：二つの極限錐の普遍性を比較し、射影後の等式で基点保存も確認する。
規約：同型そのものには Kan 性を要求しない。群への適用は別に行う。
使われ方：Goerss–Jardine VIII §1。具体的な塔の収束を通常の写像空間へ移す。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet Opposite

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) (Y : PointedSimplicialSet.{u})

/-- 通常の点つき写像空間の基礎単体集合を、具体的な骨格の塔の極限へ移す。 -/
def skeletalLimitIso : (obj K Y).right ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ ((tower K Y).obj (op n)).right)
      (fun n ↦ ((tower K Y).map (homOfLE (Nat.le_succ n)).op).right) :=
  (isLimitOfPreserves PointedSimplicialSet.forget (coneIsLimit K Y)).conePointUniqueUpToIso
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit (tower K Y ⋙ PointedSimplicialSet.forget))

/-- 同型の後の座標評価は骨格への通常の制限。 -/
@[reassoc]
lemma skeletalLimitIso_hom_projection (n : ℕ) :
    (skeletalLimitIso K Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ ((tower K Y).obj (op n)).right)
        (fun n ↦ ((tower K Y).map (homOfLE (Nat.le_succ n)).op).right) n =
      ((cone K Y).π.app (op n)).right :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- 同型は定数写像の基点を、段ごとの定数写像の整合族へ送る。 -/
lemma skeletalLimitIso_basepoint :
    (skeletalLimitIso K Y).hom.app _ (obj K Y).basepoint =
      PointedFibrationTower.limitBasepoint (fun n ↦ (tower K Y).obj (op n))
        (fun n ↦ (tower K Y).map (homOfLE (Nat.le_succ n)).op) := by
  apply Subtype.ext
  funext n
  have he := congrArg (fun f : (obj K Y).right ⟶ ((tower K Y).obj (op n)).right ↦
    f.app _ (obj K Y).basepoint) (skeletalLimitIso_hom_projection K Y n)
  exact he.trans (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ((cone K Y).π.app (op n)))

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
