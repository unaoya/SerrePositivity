module

public import SerrePositivity.AlgebraicGeometry.FrobeniusAdicControl

/-!
概要：Frobenius 半線形写像を、指数を p 倍する I 進商系の写像にする。
方針：イデアル冪の制御から商へ降ろし、遷移との可換性は代表元で示す。
規約：コホモロジー対象を展開せずに使える一般の加群の補題。
使われ方：実際の Čech Frobenius の I 進接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R H K : Type*} [CommRing R] [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable (I : Ideal R) (p : ℕ) [ExpChar R p] (f : H →ₛₗ[frobenius R p] K)

/-- Frobenius 半線形写像は、指数を p 倍する I 進商の写像を与える。 -/
def frobeniusSemilinearShiftedQuotientMap (n : ℕ) :
    H ⧸ (I ^ n • (⊤ : Submodule R H)) →ₛₗ[frobenius R p]
      K ⧸ (I ^ (p * n) • (⊤ : Submodule R K)) :=
  (I ^ n • (⊤ : Submodule R H)).mapQ (I ^ (p * n) • (⊤ : Submodule R K)) f
    (frobeniusSemilinear_ideal_power_control I p f n)

/-- 指数を p 倍する商写像は、元の代表の写像を降ろしたもの。 -/
@[simp] theorem frobeniusSemilinearShiftedQuotientMap_mk (n : ℕ) (x : H) :
    frobeniusSemilinearShiftedQuotientMap I p f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := rfl

/-- 指数を p 倍する Frobenius 商写像は、I 進遷移と可換。 -/
theorem frobeniusSemilinearShiftedQuotientMap_transition (i j : ℕ) (h : j ≤ i) :
    (AdicCompletion.transitionMap I K (Nat.mul_le_mul_left p h)).comp
        (frobeniusSemilinearShiftedQuotientMap I p f i) =
      (frobeniusSemilinearShiftedQuotientMap I p f j).comp
        (AdicCompletion.transitionMap I H h) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (I ^ i • (⊤ : Submodule R H)) x (fun m ↦ ?_)
  rfl

/-- 完備化上の Frobenius 半線形写像は、元の加群からの写像を保つ。 -/
theorem frobeniusSemilinearCompletionMap_of (x : H) :
    frobeniusSemilinearCompletionMap I p f (AdicCompletion.of I H x) =
      AdicCompletion.of I K (f x) := by
  apply Subtype.ext
  funext n
  rfl

end SerrePositivity.AlgebraicGeometry
