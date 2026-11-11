module

public import SerrePositivity.KST.Spectra.PointedTowerDifferential
public import SerrePositivity.KST.Spectra.PointedFibrationExactness

/-!
概要：塔の fiber 微分の完全性で次段への障害を補正する。
方針：連結射の値が cocycle となることを示し、その原像の fiber 包含を引く。
規約：一段下への射影を保つ。完全性は fiber の二つの微分の間で指定する。
使われ方：Goerss–Jardine VIII §§1–2。骨格の塔の像の安定化の幾何的な工程。
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

/-- 次段への連結射の値は fiber 微分の cocycle。 -/
lemma connecting_differential_eq_one (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X (n + 1)).right (r + 2) (X (n + 1)).basepoint) :
    differential X p (n + 1) r (pointedConnectingHom (p (n + 1)) (r + 1) a) = 1 := by
  rw [differential_apply, pointedConnectingHom_inclusion, map_one]

/-- fiber 微分の cocycle が境界なら、一段下への射影を保って次段へ持ち上げられる。 -/
theorem exists_lift_preserving_projection (n r : ℕ)
    (hex : ∀ z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p (n + 1))).right (r + 1)
        (pointedFiber (p (n + 1))).basepoint,
      differential X p (n + 1) r z = 1 →
        ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right (r + 2)
            (pointedFiber (p n)).basepoint,
          differential X p n (r + 1) c = z)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X (n + 1)).right (r + 2) (X (n + 1)).basepoint) :
    ∃ b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X (n + 2)).right (r + 2) (X (n + 2)).basepoint,
      pointedGroupMap (r + 2) (p n) (pointedGroupMap (r + 2) (p (n + 1)) b) =
        pointedGroupMap (r + 2) (p n) a := by
  obtain ⟨c, hc⟩ := hex (pointedConnectingHom (p (n + 1)) (r + 1) a)
    (connecting_differential_eq_one X p n r a)
  let ic := pointedGroupMap (r + 2) (pointedFiberι (p n)) c
  have hδ : pointedConnectingHom (p (n + 1)) (r + 1) (a * ic⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change pointedConnectingHom (p (n + 1)) (r + 1) a *
      (differential X p n (r + 1) c)⁻¹ = 1
    rw [hc, mul_inv_cancel]
  obtain ⟨b, hb⟩ := (pointed_exact_total_base (p (n + 1)) (r + 1) (a * ic⁻¹)).1 hδ
  refine ⟨b, ?_⟩
  rw [hb, map_mul, map_inv]
  have hi : pointedGroupMap (r + 2) (p n) ic = 1 :=
    (pointed_exact_fiber_total (p n) (r + 2) ic).2 ⟨c, rfl⟩
  rw [hi, inv_one, mul_one]

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
