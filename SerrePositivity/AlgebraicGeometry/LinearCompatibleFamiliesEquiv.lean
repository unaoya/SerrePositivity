module

public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamiliesMap

/-!
概要：遷移と可換な成分ごとの線形同型を、互換族の線形同型へまとめる。
方針：逆写像の可換性を同型の単射性で導き、両方の合成を成分で確かめる。
規約：係数環は固定する。
使われ方：二重閉厚化の Čech 比較を、逆極限の互換族へ送る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type*} [CommRing R] {Q P : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (s : ∀ i j : ℕ, j ≤ i → P i →ₗ[R] P j)
variable (e : ∀ n, Q n ≃ₗ[R] P n)
variable (he : ∀ i j (h : j ≤ i), (s i j h).comp (e i).toLinearMap =
  (e j).toLinearMap.comp (t i j h))
include he

/-- 互換な成分同型の逆写像も、逆向きに遷移と可換。 -/
theorem compatibleLinearFamiliesEquiv_inverse_commute (i j : ℕ) (h : j ≤ i) :
    (t i j h).comp (e i).symm.toLinearMap = (e j).symm.toLinearMap.comp (s i j h) := by
  apply LinearMap.ext
  intro x
  apply (e j).injective
  have hc := DFunLike.congr_fun (he i j h) ((e i).symm x)
  change s i j h (e i ((e i).symm x)) = e j (t i j h ((e i).symm x)) at hc
  rw [LinearEquiv.apply_symm_apply] at hc
  change e j (t i j h ((e i).symm x)) = e j ((e j).symm (s i j h x))
  rw [LinearEquiv.apply_symm_apply]
  exact hc.symm

/-- 成分ごとの互換な線形同型が誘導する、互換族の線形同型。 -/
def compatibleLinearFamiliesEquiv : compatibleLinearFamilies t ≃ₗ[R] compatibleLinearFamilies s where
  toLinearMap := compatibleLinearFamiliesMap t s (fun n ↦ (e n).toLinearMap) he
  invFun := compatibleLinearFamiliesMap s t (fun n ↦ (e n).symm.toLinearMap)
    (compatibleLinearFamiliesEquiv_inverse_commute t s e he)
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (e n).symm_apply_apply (x.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (e n).apply_symm_apply (x.val n)

/-- 互換族の同型の成分は、もとの成分同型で計算できる。 -/
@[simp] theorem compatibleLinearFamiliesEquiv_apply (x : compatibleLinearFamilies t) (n : ℕ) :
    (compatibleLinearFamiliesEquiv t s e he x).val n = e n (x.val n) := rfl

end SerrePositivity.AlgebraicGeometry
