module

public import SerrePositivity.KST.Spectra.PointedTowerDifferential
public import SerrePositivity.KST.Spectra.SkeletalMappingFiber

/-!
概要：骨格の写像空間の塔の実際の fiber 間の最初の微分。
方針：隣接骨格への制限が Kan fibration であることを使って塔の微分を適用する。
規約：cochain の交代式との照合は別途行う。
使われ方：Goerss–Jardine VIII §1。有理 Shapiro の骨格の塔の微分。
-/

@[expose] public section

universe u

open CategoryTheory Opposite SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : SSet.{u}) (X : PointedSimplicialSet.{u}) [KanComplex X.right]

/-- 概要：n 骨格から n+1 骨格へ進む fiber と次の fiber の群の微分。
方針：実際の制限の fiber の包含と次の制限の連結準同型を合成する。
規約：実際のホモトピー次数は r+2 から r+1 へ下がる。
使われ方：Goerss–Jardine VIII §1。セルの係数表示へ移す幾何的な微分。 -/
def stageDifferential (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K X n).right (r + 1) (stageFiber K X n).basepoint →*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K X (n + 1)).right r (stageFiber K X (n + 1)).basepoint := by
  let p := fun m ↦ (tower K X).map (homOfLE (Nat.le_succ m)).op
  let : ∀ m, Fibration (p m).right := fun m ↦ tower_map_fibration K X _
  exact PointedFibrationTower.differential (fun m ↦ (tower K X).obj (op m)) p n r

/-- 概要：骨格の塔の fiber の幾何的な微分の二乗は自明。
方針：点つき fibration の塔の零合成をそのまま適用する。
規約：乗法記法で自明な値は単位。塔の収束を要求しない。
使われ方：Goerss–Jardine VIII §1。E_1 の複体条件。 -/
@[simp]
theorem stageDifferential_comp (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K X n).right (r + 2) (stageFiber K X n).basepoint) :
    stageDifferential K X (n + 1) r (stageDifferential K X n (r + 1) a) = 1 := by
  let p := fun m ↦ (tower K X).map (homOfLE (Nat.le_succ m)).op
  let : ∀ m, Fibration (p m).right := fun m ↦ tower_map_fibration K X _
  exact PointedFibrationTower.differential_comp (fun m ↦ (tower K X).obj (op m)) p n r a

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
