module

public import SerrePositivity.AlgebraicGeometry.AdicProjectionFactor
public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamiliesMap
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
概要：I 進完備化から互換族への標準写像は、可換な係数写像に自然である。
方針：Iⁿ による商上で可換性を確かめ、完備化の各成分で評価する。
規約：ここでは基底環とイデアルを固定し、加群と射影先を変える。
使われ方：Čech 形式関数の同型を、共通細分や係数写像と可換にする土台。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R H K : Type*} [CommRing R]
variable [AddCommGroup H] [Module R H] [AddCommGroup K] [Module R K]
variable (I : Ideal R) {Q P : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
variable (π : ∀ n, H →ₗ[R] Q n) (ρ : ∀ n, K →ₗ[R] P n)
variable (hpowπ : ∀ n, I ^ n • (⊤ : Submodule R H) ≤ LinearMap.ker (π n))
variable (hpowρ : ∀ n, I ^ n • (⊤ : Submodule R K) ≤ LinearMap.ker (ρ n))
variable (f : H →ₗ[R] K) (g : ∀ n, Q n →ₗ[R] P n)
variable (hproj : ∀ n, (g n).comp (π n) = (ρ n).comp f)
include hproj

/-- 射影の可換性は、I 進剰余類上へ降ろした射影にも成り立つ。 -/
theorem adicProjectionQuotientMap_naturality (n : ℕ) :
    (g n).comp (adicProjectionQuotientMap I π hpowπ n) =
      (adicProjectionQuotientMap I ρ hpowρ n).comp
        ((f.reduceModIdeal (I ^ n)).restrictScalars R) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (I ^ n • (⊤ : Submodule R H)) x (fun m ↦ ?_)
  exact DFunLike.congr_fun (hproj n) m

variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (s : ∀ i j : ℕ, j ≤ i → P i →ₗ[R] P j)
variable (hπ : ∀ i j (h : j ≤ i), (t i j h).comp (π i) = π j)
variable (hρ : ∀ i j (h : j ≤ i), (s i j h).comp (ρ i) = ρ j)
variable (hg : ∀ i j (h : j ≤ i), (s i j h).comp (g i) = (g j).comp (t i j h))

/-- 完備化から互換族への標準写像は、成分写像と可換。 -/
theorem adicProjectionCompletionMap_naturality_apply (a : AdicCompletion I H) :
    compatibleLinearFamiliesMap t s g hg (adicProjectionCompletionMap I π hpowπ t hπ a) =
      adicProjectionCompletionMap I ρ hpowρ s hρ (AdicCompletion.map I f a) := by
  apply Subtype.ext
  funext n
  change g n (adicProjectionQuotientMap I π hpowπ n (a.val n)) =
    adicProjectionQuotientMap I ρ hpowρ n (f.reduceModIdeal (I ^ n) (a.val n))
  exact DFunLike.congr_fun (adicProjectionQuotientMap_naturality
    I π ρ hpowπ hpowρ f g hproj n) (a.val n)

end SerrePositivity.AlgebraicGeometry
