module

public import SerrePositivity.KST.Spectra.TowerCompatibleDetection

/-!
概要：最初の fiber の cocycle が零なら、整合族は初段の値から検出できる。
方針：初段で零な類を fiber の像へ戻し、次段への持ち上げから最初の微分の零性を得る。
規約：高い段は既証の段一での検出に渡す。
使われ方：Goerss–Jardine VIII §2。有理写像空間の零骨格での検出。
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
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)
  (hex : ∀ n, ∀ z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p (n + 1))).right (r + 1)
      (pointedFiber (p (n + 1))).basepoint,
    differential X p (n + 1) r z = 1 →
      ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p n)).right (r + 2)
          (pointedFiber (p n)).basepoint,
        differential X p n (r + 1) c = z)
  (hfirst : ∀ z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (pointedFiber (p 0)).right (r + 1)
      (pointedFiber (p 0)).basepoint, differential X p 0 r z = 1 → z = 1)

include hex hfirst in
/-- 初段で零となる整合族は単位元。 -/
theorem compatibleGroup_eq_one_of_stage_zero
    (a : compatibleGroup X p (r + 1)) (h0 : a.val 0 = 1) : a = 1 := by
  have hp : pointedGroupMap (r + 1) (p 0) (a.val 1) = 1 := (a.property 0).trans h0
  obtain ⟨c, hc⟩ := (pointed_exact_fiber_total (p 0) (r + 1) _).1 hp
  have hd : differential X p 0 r c = 1 := by
    rw [differential_apply, hc, ← a.property 1, pointedConnectingHom_projection]
  have h1 : a.val 1 = 1 := by rw [← hc, hfirst c hd, map_one]
  exact compatibleGroup_eq_one_of_stage_one X p r hex a h1

include hex hfirst in
/-- 高次の fiber 完全性と最初の fiber の消滅から、初段での評価の単射性を得る。 -/
theorem compatibleGroup_stage_zero_injective :
    Function.Injective (fun a : compatibleGroup X p (r + 1) ↦ a.val 0) := by
  intro a b hab
  change a.val 0 = b.val 0 at hab
  have h0 : (a * b⁻¹).val 0 = 1 := by
    change a.val 0 * (b.val 0)⁻¹ = 1
    rw [hab, mul_inv_cancel]
  exact mul_inv_eq_one.mp
    (compatibleGroup_eq_one_of_stage_zero X p r hex hfirst (a * b⁻¹) h0)

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
