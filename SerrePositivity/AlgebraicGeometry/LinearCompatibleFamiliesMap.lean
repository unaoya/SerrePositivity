module

public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamilies

/-!
概要：遷移と可換な成分写像から、互換族の間の線形写像を作る。
方針：成分ごとの写像を積へ適用し、可換式で互換性を確かめる。
規約：係数環を固定する。
使われ方：完備化の比較を、係数写像や共通細分に自然な形で述べる。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type*} [Semiring R] {Q P : ℕ → Type*}
variable [∀ n, AddCommMonoid (Q n)] [∀ n, Module R (Q n)]
variable [∀ n, AddCommMonoid (P n)] [∀ n, Module R (P n)]
variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (s : ∀ i j : ℕ, j ≤ i → P i →ₗ[R] P j)
variable (f : ∀ n, Q n →ₗ[R] P n)
variable (hf : ∀ i j (h : j ≤ i), (s i j h).comp (f i) = (f j).comp (t i j h))

/-- 遷移と可換な成分写像が誘導する、互換族の間の線形写像。 -/
def compatibleLinearFamiliesMap : compatibleLinearFamilies t →ₗ[R] compatibleLinearFamilies s where
  toFun x := ⟨fun n ↦ f n (x.val n), by
    intro i j h
    exact (DFunLike.congr_fun (hf i j h) (x.val i)).trans
      (congrArg (f j) (x.property i j h))⟩
  map_add' x y := Subtype.ext (funext fun n ↦ (f n).map_add (x.val n) (y.val n))
  map_smul' r x := Subtype.ext (funext fun n ↦ (f n).map_smul r (x.val n))

/-- 互換族の写像を成分で評価する。 -/
@[simp] theorem compatibleLinearFamiliesMap_apply (x : compatibleLinearFamilies t) (n : ℕ) :
    (compatibleLinearFamiliesMap t s f hf x).val n = f n (x.val n) := rfl

end SerrePositivity.AlgebraicGeometry
