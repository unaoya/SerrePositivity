module

public import Mathlib.LinearAlgebra.Pi

/-! # 加群の可算逆系の差分写像

直積上の恒等写像−遷移写像と、その核としての両立する列を構成する。
遷移が全射なら差分写像も全射。この代数計算をホモトピー逆極限に使う。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (M : ℕ → Type v)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n, M (n + 1) →ₗ[R] M n)

/-- 逆系の直積上の差分写像。 -/
def moduleTowerDifference : (∀ n, M n) →ₗ[R] (∀ n, M n) where
  toFun x n := x n - t n (x (n + 1))
  map_add' x y := by ext n; simp only [Pi.add_apply, map_add]; exact add_sub_add_comm _ _ _ _
  map_smul' r x := by ext n; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]

@[simp] theorem moduleTowerDifference_apply (x : ∀ n, M n) (n : ℕ) :
    moduleTowerDifference R M t x n = x n - t n (x (n + 1)) := rfl

/-- 両立する列の加群。 -/
def moduleTowerLimit : Submodule R (∀ n, M n) := (moduleTowerDifference R M t).ker

/-- 差分写像の核に入ることは、隣接段の両立性と同値。 -/
theorem mem_moduleTowerLimit_iff (x : ∀ n, M n) :
    x ∈ moduleTowerLimit R M t ↔ ∀ n, t n (x (n + 1)) = x n := by
  change moduleTowerDifference R M t x = 0 ↔ _
  simp only [funext_iff, moduleTowerDifference_apply, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' (fun n ↦ eq_comm)

/-- 遷移写像が全射なら、直積上の差分写像も全射。 -/
theorem moduleTowerDifference_surjective (ht : ∀ n, Function.Surjective (t n)) :
    Function.Surjective (moduleTowerDifference R M t) := by
  intro y
  let x : ∀ n, M n := fun n ↦ Nat.rec (motive := fun k ↦ M k) 0
    (fun k a ↦ Classical.choose (ht k (a - y k))) n
  refine ⟨x, ?_⟩
  ext n
  have hx : t n (x (n + 1)) = x n - y n := by
    exact Classical.choose_spec (ht n (x n - y n))
  rw [moduleTowerDifference_apply, hx, sub_sub_cancel]

/-- 両立する列の第n成分への射影。 -/
def moduleTowerProjection (n : ℕ) : moduleTowerLimit R M t →ₗ[R] M n :=
  (LinearMap.proj n).comp (moduleTowerLimit R M t).subtype

/-- 射影と遷移写像は可換。 -/
theorem moduleTowerProjection_compatible (n : ℕ) :
    (t n).comp (moduleTowerProjection R M t (n + 1)) = moduleTowerProjection R M t n := by
  ext x
  exact (mem_moduleTowerLimit_iff R M t x.val).mp x.property n

/-- 両立する写像の族から逆極限への線形写像を構成する。 -/
def moduleTowerLimitLift (N : Type*) [AddCommGroup N] [Module R N]
    (g : ∀ n, N →ₗ[R] M n) (hg : ∀ n, (t n).comp (g (n + 1)) = g n) :
    N →ₗ[R] moduleTowerLimit R M t where
  toFun x := ⟨fun n ↦ g n x, (mem_moduleTowerLimit_iff R M t _).mpr
    (fun n ↦ LinearMap.congr_fun (hg n) x)⟩
  map_add' x y := by apply Subtype.ext; ext n; exact (g n).map_add x y
  map_smul' r x := by apply Subtype.ext; ext n; exact (g n).map_smul r x

@[simp] theorem moduleTowerProjection_comp_lift (N : Type*) [AddCommGroup N] [Module R N]
    (g : ∀ n, N →ₗ[R] M n) (hg : ∀ n, (t n).comp (g (n + 1)) = g n) (n : ℕ) :
    (moduleTowerProjection R M t n).comp (moduleTowerLimitLift R M t N g hg) = g n := rfl

/-- すべての射影を指定すれば、逆極限への写像は一意。 -/
theorem moduleTowerLimitLift_unique (N : Type*) [AddCommGroup N] [Module R N]
    (g : ∀ n, N →ₗ[R] M n) (hg : ∀ n, (t n).comp (g (n + 1)) = g n)
    (f : N →ₗ[R] moduleTowerLimit R M t)
    (hf : ∀ n, (moduleTowerProjection R M t n).comp f = g n) :
    f = moduleTowerLimitLift R M t N g hg := by
  ext x n
  exact LinearMap.congr_fun (hf n) x

end SerrePositivity.DerivedCompletion
