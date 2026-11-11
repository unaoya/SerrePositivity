module

public import SerrePositivity.KST.Spectra.SkeletalFiberDifferential
public import SerrePositivity.KST.Spectra.UnbasedMappingPost
public import SerrePositivity.KST.Spectra.PointedTowerDifferentialNaturality

/-!
概要：骨格の塔の実際の fiber の係数射と幾何的微分の自然性。
方針：係数の後合成による塔の可換正方形を fiber と連結準同型へ送る。
規約：源の単体集合の Kan 性は不要。係数は Kan。
使われ方：Goerss–Jardine VIII §1。cochain と幾何的微分の自然な比較。
-/

@[expose] public section

universe u

open CategoryTheory Opposite SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：係数の点つき射が誘導する骨格の tower fiber の射。
方針：隣接骨格の制限と後合成の可換正方形の点つき fiber の射を取る。
規約：構成自体は係数の Kan 性を使わない。
使われ方：Goerss–Jardine VIII §1。骨格の fiber の関手性。 -/
def stageFiberMap (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) (n : ℕ) :
    stageFiber K Y n ⟶ stageFiber K Z n :=
  PointedFiberComparison.map
    ((tower K Y).map (homOfLE (Nat.le_succ n)).op)
    ((tower K Z).map (homOfLE (Nat.le_succ n)).op)
    ((towerPost K p).app (op (n + 1))) ((towerPost K p).app (op n))
    ((towerPost K p).naturality (homOfLE (Nat.le_succ n)).op)

/-- 概要：骨格の tower fiber の幾何的微分は係数射と可換。
方針：実際の塔の射へ、fibration の塔の微分の自然性を適用する。
規約：基点は定数射、群の次数は正次数。
使われ方：Goerss–Jardine VIII §1。E_1 の係数の自然性。 -/
theorem stageDifferential_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K Y n).right (r + 1) (stageFiber K Y n).basepoint) :
    pointedGroupMap (X := stageFiber K Y (n + 1)) (Y := stageFiber K Z (n + 1)) r
      (stageFiberMap K (Y := Y) (Z := Z) p (n + 1)) (stageDifferential K Y n r a) =
      stageDifferential K Z n r (pointedGroupMap
        (X := stageFiber K Y n) (Y := stageFiber K Z n) (r + 1)
          (stageFiberMap K (Y := Y) (Z := Z) p n) a) := by
  let py := fun m ↦ (tower K Y).map (homOfLE (Nat.le_succ m)).op
  let pz := fun m ↦ (tower K Z).map (homOfLE (Nat.le_succ m)).op
  let : ∀ m, Fibration (py m).right := fun m ↦ tower_map_fibration K Y _
  let : ∀ m, Fibration (pz m).right := fun m ↦ tower_map_fibration K Z _
  exact PointedFibrationTower.differential_natural
    (X := fun m ↦ (tower K Y).obj (op m)) (Y := fun m ↦ (tower K Z).obj (op m)) py pz
    (fun m ↦ (towerPost K p).app (op m))
    (fun m ↦ (towerPost K p).naturality (homOfLE (Nat.le_succ m)).op) n r a

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
