module

public import SerrePositivity.KST.Spectra.PointedTowerDifferential
public import SerrePositivity.KST.Spectra.PointedFibrationNaturality

/-!
概要：点つき fibration の塔の最初の fiber 微分の自然性。
方針：隣り合う二つの可換正方形で、連結射の自然性と fiber 包含の式を合成する。
規約：段の射と遷移が厳密に可換であることを要求する。
使われ方：Goerss–Jardine VIII §1。骨格の塔の係数射への自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : ℕ → PointedSimplicialSet.{u}}
  (p : ∀ n, X (n + 1) ⟶ X n) (q : ∀ n, Y (n + 1) ⟶ Y n)
  [∀ n, KanComplex (X n).right] [∀ n, KanComplex (Y n).right]
  [∀ n, Fibration (p n).right] [∀ n, Fibration (q n).right]
  (f : ∀ n, X n ⟶ Y n) (h : ∀ n, p n ≫ f n = f (n + 1) ≫ q n)

/-- 概要：塔の厳密な射で最初の fiber 微分は可換。
方針：次の fibration の連結準同型の自然性を前の fiber 包含の正方形と合成する。
規約：fiber の射は隣接段の可換正方形から直接構成する。
使われ方：Goerss–Jardine VIII §1。実際の幾何的微分の自然性。 -/
theorem differential_natural (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right (r + 1) (pointedFiber (p n)).basepoint) :
    pointedGroupMap r
      (PointedFiberComparison.map (p (n + 1)) (q (n + 1)) (f (n + 2)) (f (n + 1)) (h (n + 1)))
      (differential X p n r a) =
    differential Y q n r (pointedGroupMap (r + 1)
      (PointedFiberComparison.map (p n) (q n) (f (n + 1)) (f n) (h n)) a) := by
  rw [differential_apply, differential_apply, pointedConnectingHom_natural]
  have hg := congrArg (fun k ↦ pointedGroupMap (r + 1) k a)
    (PointedFiberComparison.map_ι (p n) (q n) (f (n + 1)) (f n) (h n))
  simp only [pointedGroupMap_comp] at hg
  rw [hg]

end

end SerrePositivity.KST.Spectra.PointedFibrationTower
