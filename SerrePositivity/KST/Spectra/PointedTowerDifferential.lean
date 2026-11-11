module

public import SerrePositivity.KST.Spectra.PointedFibrationBoundary

/-!
概要：点つき Kan fibration の塔の fiber の群の最初の微分。
方針：fiber 包含の後で次の段の連結準同型を適用し、零合成で二乗の零性を示す。
規約：交代 cochain 微分との一致と塔の収束はここでは主張しない。
使われ方：Goerss–Jardine VIII §1。骨格の塔の exact couple の最初の群の射。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right]

/-- 概要：塔の隣接する二つの fiber の群の微分。
方針：前の fiber を共通の段へ含め、次の fibration の連結準同型を合成する。
規約：π_(r+2)(F_n) から π_(r+1)(F_(n+1)) へ向かう。
使われ方：Goerss–Jardine VIII §1。骨格の cochain 微分との比較の始点。 -/
def differential (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right (r + 1) (pointedFiber (p n)).basepoint →*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p (n + 1))).right r
        (pointedFiber (p (n + 1))).basepoint :=
  (pointedConnectingHom (p (n + 1)) r).comp
    (pointedGroupMap (r + 1) (pointedFiberι (p n)))

lemma differential_apply (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right (r + 1)
      (pointedFiber (p n)).basepoint) :
    differential X p n r a = pointedConnectingHom (p (n + 1)) r
      (pointedGroupMap (r + 1) (pointedFiberι (p n)) a) := rfl

/-- 概要：fiber の微分を包含した像は自明。
方針：連結準同型と fiber 包含の零合成を使う。
規約：乗法記法で自明な値は単位。
使われ方：Goerss–Jardine VIII §1。最初の微分の二乗の零性。 -/
@[simp]
lemma differential_inclusion (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right (r + 1)
      (pointedFiber (p n)).basepoint) :
    pointedGroupMap r (pointedFiberι (p (n + 1))) (differential X p n r a) = 1 := by
  rw [differential_apply, pointedConnectingHom_inclusion]

/-- 概要：塔の fiber の群の最初の微分の二乗は自明。
方針：間に現れる連結準同型の後の包含の像が単位となることを使う。
規約：次数は各微分で一つ下がる。収束の主張は含まない。
使われ方：Goerss–Jardine VIII §1。E_1 の複体条件の幾何的な入力。 -/
@[simp]
theorem differential_comp (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right (r + 2)
      (pointedFiber (p n)).basepoint) :
    differential X p (n + 1) r (differential X p n (r + 1) a) = 1 := by
  rw [differential_apply, differential_inclusion, map_one]

end

end SerrePositivity.KST.Spectra.PointedFibrationTower
