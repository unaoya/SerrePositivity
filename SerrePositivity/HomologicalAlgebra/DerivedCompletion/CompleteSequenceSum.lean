module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalReflectionPresentation
public import Mathlib.Tactic.Ring

/-! # 導来完備加群における列の和と交差する重み

漸化式の一意解から列の和を作り、二座標Koszulの交差境界に必要な重みの比較を行う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- f導来完備加群の列を、漸化式の一意解の始値へ送る。 -/
def completeSequenceSum (f : R) (N : ModuleCat.{u} R) (hN : IsModuleComplete R f N) :
    (ℕ → N) →ₗ[R] N :=
  (LinearMap.proj 0).comp (adicRecurrenceEquiv R f N hN).symm.toLinearMap

/-- 漸化式の像の和は、元の列の始値。 -/
@[simp] theorem completeSequenceSum_recurrence (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (x : ℕ → N) :
    completeSequenceSum R f N hN (adicRecurrenceMap f x) = x 0 :=
  congrFun ((adicRecurrenceEquiv R f N hN).symm_apply_apply x) 0

/-- 和を、最初の項とf倍した残りの和へ分解する。 -/
theorem completeSequenceSum_decomposition (f : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) (x : ℕ → N) :
    completeSequenceSum R f N hN x =
      x 0 + f • completeSequenceSum R f N hN (fun n ↦ x (n + 1)) := by
  let y := (adicRecurrenceEquiv R f N hN).symm x
  have hy : adicRecurrenceMap f y = x := (adicRecurrenceEquiv R f N hN).apply_symm_apply x
  have ht : adicRecurrenceMap f (fun n ↦ y (n + 1)) = fun n ↦ x (n + 1) := by
    funext n
    exact congrFun hy (n + 1)
  have hs : completeSequenceSum R f N hN (fun n ↦ x (n + 1)) = y 1 := by
    rw [← ht, completeSequenceSum_recurrence]
  rw [hs]
  change y 0 = x 0 + f • y 1
  have h := congrFun hy 0
  change y 0 - f • y 1 = x 0 at h
  exact sub_eq_iff_eq_add.mp h

/-- f導来完備なら、fの任意の倍数についても導来完備。 -/
theorem isModuleComplete_mul_right (f b : R) (N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) : IsModuleComplete R (f * b) N := by
  have hf := (isModuleComplete_iff_recurrence_bijective R f N).mp hN
  apply (isModuleComplete_iff_recurrence_bijective R (f * b) N).mpr
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    funext n
    let z : ℕ → N := fun k ↦ b ^ k • x (n + k)
    have hz : adicRecurrenceMap f z = 0 := by
      funext k
      change b ^ k • x (n + k) - f • (b ^ (k + 1) • x (n + (k + 1))) = 0
      rw [smul_smul, pow_succ]
      have he : f * (b ^ k * b) = b ^ k * (f * b) := by ring
      rw [he, ← smul_smul, ← smul_sub]
      have h := congrFun hx (n + k)
      change x (n + k) - (f * b) • x (n + k + 1) = 0 at h
      rw [show n + (k + 1) = n + k + 1 by omega, h, smul_zero]
    have he := hf.injective (hz.trans (map_zero _).symm)
    simpa [z] using congrFun he 0
  · intro y
    let x : ℕ → N := fun n ↦ completeSequenceSum R f N hN
      (fun k ↦ b ^ k • y (n + k))
    refine ⟨x, ?_⟩
    funext n
    have h := completeSequenceSum_decomposition R f N hN (fun k ↦ b ^ k • y (n + k))
    have ht : (fun k ↦ b ^ (k + 1) • y (n + (k + 1))) =
        b • (fun k ↦ b ^ k • y ((n + 1) + k)) := by
      funext k
      simp only [Pi.smul_apply, smul_smul, pow_succ]
      rw [mul_comm b (b ^ k), show n + (k + 1) = (n + 1) + k by omega]
    rw [ht, map_smul] at h
    simp only [pow_zero, one_smul, Nat.add_zero, smul_smul] at h
    change x n - (f * b) • x (n + 1) = y n
    exact sub_eq_iff_eq_add.mpr h

/-- 二つの重みを同じ列へ掛ける和は、積の元に関する和と一致する。 -/
theorem completeSequenceSum_weighted (a b : R) (N : ModuleCat.{u} R)
    (hb : IsModuleComplete R b N) (hab : IsModuleComplete R (a * b) N) (z : ℕ → N) :
    completeSequenceSum R b N hb (fun n ↦ a ^ n • z n) =
      completeSequenceSum R (a * b) N hab z := by
  let x := (adicRecurrenceEquiv R (a * b) N hab).symm z
  have hx : adicRecurrenceMap (a * b) x = z :=
    (adicRecurrenceEquiv R (a * b) N hab).apply_symm_apply z
  have hw : adicRecurrenceMap b (fun n ↦ a ^ n • x n) = fun n ↦ a ^ n • z n := by
    funext n
    change a ^ n • x n - b • (a ^ (n + 1) • x (n + 1)) = a ^ n • z n
    rw [smul_smul, pow_succ]
    rw [show b * (a ^ n * a) = a ^ n * (a * b) by ring, ← smul_smul, ← smul_sub]
    exact congrArg (fun v : N ↦ a ^ n • v) (congrFun hx n)
  rw [← hw, completeSequenceSum_recurrence]
  simp [completeSequenceSum, x]

/-- 二座標の交差境界を消す、重み付きの和の交換。 -/
theorem completeSequenceSum_cross (f d : R) (N : ModuleCat.{u} R)
    (hf : IsModuleComplete R f N) (hd : IsModuleComplete R d N) (z : ℕ → N) :
    completeSequenceSum R d N hd (fun n ↦ f ^ n • z n) =
      completeSequenceSum R f N hf (fun n ↦ d ^ n • z n) := by
  have hfd := isModuleComplete_mul_right R f d N hf
  have hdf : IsModuleComplete R (d * f) N := by simpa [mul_comm d f] using hfd
  rw [completeSequenceSum_weighted R f d N hd hfd,
    completeSequenceSum_weighted R d f N hf hdf]
  congr 2
  exact mul_comm f d

end SerrePositivity.DerivedCompletion
