module

public import SerrePositivity.KST.Spectra.TowerGroupLimitComparison
public import SerrePositivity.KST.Spectra.TowerDifferentialCorrection

/-!
概要：fiber 微分の完全性で、塔の整合族の群を第二段の値から検出する。
方針：前段で零な整合族を fiber の像へ戻し、次段への持ち上げから cocycle 条件を得る。
規約：第一の fiber はまだ扱わず、段一で零なら全段で零と証明する。
使われ方：Goerss–Jardine VIII §1。整合族を初段の係数へ同定する帰納工程。
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

include hex in
/-- 段一で零となる整合族は、全ての段で零になる。 -/
theorem compatibleGroup_eq_one_of_stage_one
    (a : compatibleGroup X p (r + 1)) (h1 : a.val 1 = 1) : a = 1 := by
  have ha : ∀ n, a.val (n + 1) = 1 := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih =>
      have hp : pointedGroupMap (r + 1) (p (n + 1)) (a.val (n + 2)) = 1 :=
        (a.property (n + 1)).trans ih
      obtain ⟨c, hc⟩ := (pointed_exact_fiber_total (p (n + 1)) (r + 1) _).1 hp
      have hd : differential X p (n + 1) r c = 1 := by
        rw [differential_apply, hc, ← a.property (n + 2), pointedConnectingHom_projection]
      obtain ⟨b, hb⟩ := hex n c hd
      rw [← hc, ← hb, differential_inclusion]
  apply Subtype.ext
  funext n
  cases n with
  | zero =>
    change a.val 0 = 1
    rw [← a.property 0, ha 0, map_one]
  | succ n => exact ha n

include hex in
/-- fiber 微分が完全なら、整合族の段一での評価は単射。 -/
theorem compatibleGroup_stage_one_injective :
    Function.Injective (fun a : compatibleGroup X p (r + 1) ↦ a.val 1) := by
  intro a b hab
  change a.val 1 = b.val 1 at hab
  have h1 : (a * b⁻¹).val 1 = 1 := by
    change a.val 1 * (b.val 1)⁻¹ = 1
    rw [hab, mul_inv_cancel]
  exact mul_inv_eq_one.mp (compatibleGroup_eq_one_of_stage_one X p r hex (a * b⁻¹) h1)

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
