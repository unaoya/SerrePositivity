module

public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamilies

/-!
概要：異なる係数環の互換族の間に、半線形な成分写像を送る。
方針：成分ごとの可換式を積の部分加群へ適用する。
規約：係数環の準同型を半線形性に明示する。
使われ方：底変換と Frobenius に対する Čech 形式関数の自然性。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry
variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S)
variable {Q P : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable [∀ n, AddCommGroup (P n)] [∀ n, Module S (P n)]
variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (s : ∀ i j : ℕ, j ≤ i → P i →ₗ[S] P j)
variable (f : ∀ n, Q n →ₛₗ[σ] P n)
variable (hf : ∀ i j (h : j ≤ i), (s i j h).comp (f i) = (f j).comp (t i j h))

/-- 遷移と可換な半線形成分写像が誘導する、互換族の半線形写像。 -/
def compatibleSemilinearFamiliesMap :
    compatibleLinearFamilies t →ₛₗ[σ] compatibleLinearFamilies s where
  toFun x := ⟨fun n ↦ f n (x.val n), by
    intro i j h
    exact (DFunLike.congr_fun (hf i j h) (x.val i)).trans
      (congrArg (f j) (x.property i j h))⟩
  map_add' x y := Subtype.ext (funext fun n ↦ (f n).map_add (x.val n) (y.val n))
  map_smul' r x := Subtype.ext (funext fun n ↦ map_smulₛₗ (f n) r (x.val n))

/-- 半線形な互換族の写像を、各成分で評価する。 -/
@[simp] theorem compatibleSemilinearFamiliesMap_apply
    (x : compatibleLinearFamilies t) (n : ℕ) :
    (compatibleSemilinearFamiliesMap σ t s f hf x).val n = f n (x.val n) := rfl

end SerrePositivity.AlgebraicGeometry
