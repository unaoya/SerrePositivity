module

public import SerrePositivity.KST.Spectra.PointedZeroConnectingNaturality
public import SerrePositivity.KST.Spectra.PointedHomotopy
public import SerrePositivity.KST.Spectra.PointedTowerLoopDifferential

/-!
概要：fibration の塔の基本群から次の fiber の成分集合への微分。
方針：fiber 包含と零次数接続写像を合成し、可換正方形への自然性を使う。
規約：零次数の出力には群演算を入れない。
使われ方：Goerss–Jardine VIII §1。loop による微分の次数移動の基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 基本群の元の fiber 包含の像に次の零次数接続写像を適用する。 -/
def differentialZero (X : ℕ → PointedSimplicialSet.{u})
    (p : ∀ n, X (n + 1) ⟶ X n)
    [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right 0 (pointedFiber (p n)).basepoint →
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (pointedFiber (p (n + 1))).right 0 (pointedFiber (p (n + 1))).basepoint :=
  fun a ↦ pointedConnectingZero (p (n + 1)) (pointedGroupMap 0 (pointedFiberι (p n)) a)

/-- 概要：塔の厳密な射は零次数の微分と可換。
方針：次の段の零次数接続写像と、前の段の fiber 包含の自然性を合成する。
規約：成分集合での等式。
使われ方：Goerss–Jardine VIII §1。骨格の塔の模型を交換する界面。 -/
theorem differentialZero_natural {X Y : ℕ → PointedSimplicialSet.{u}}
    (p : ∀ n, X (n + 1) ⟶ X n) (q : ∀ n, Y (n + 1) ⟶ Y n)
    [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
    [∀ n, Fibration (p n).right] [∀ n, Fibration (q n).right]
    (f : ∀ n, X n ⟶ Y n) (h : ∀ n, p n ≫ f n = f (n + 1) ≫ q n) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right 0 (pointedFiber (p n)).basepoint) :
    pointedHomotopyMap 0
      (PointedFiberComparison.map (p (n + 1)) (q (n + 1)) (f (n + 2)) (f (n + 1)) (h (n + 1)))
      (differentialZero X p n a) =
    differentialZero Y q n (pointedGroupMap 0
      (PointedFiberComparison.map (p n) (q n) (f (n + 1)) (f n) (h n)) a) := by
  dsimp only [differentialZero, pointedHomotopyMap]
  rw [pointedConnectingZero_natural]
  have hg := congrArg (fun k ↦ pointedGroupMap 0 k a)
    (PointedFiberComparison.map_ι (p n) (q n) (f (n + 1)) (f n) (h n))
  simp only [pointedGroupMap_comp] at hg
  rw [hg]

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
