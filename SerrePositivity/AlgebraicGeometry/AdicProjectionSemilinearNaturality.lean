module

public import SerrePositivity.AlgebraicGeometry.AdicProjectionFactor
public import SerrePositivity.AlgebraicGeometry.AdicSemilinearMap
public import SerrePositivity.AlgebraicGeometry.SemilinearCompatibleFamiliesMap

/-!
概要：完備化から互換族への標準写像は、異なる係数環の半線形写像にも自然である。
方針：剰余類の半線形写像で四角形を示し、完備化の各成分で評価する。
規約：flat 性を仮定せず、必要なイデアル冪の包含を明示する。
使われ方：§9 の底変換・閉厚化・Frobenius の可換図式の共通部分。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R S H K : Type*} [CommRing R] [CommRing S]
variable [AddCommGroup H] [Module R H] [AddCommGroup K] [Module S K]
variable (I : Ideal R) (J : Ideal S) {σ : R →+* S} {Q P : ℕ → Type*}
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable [∀ n, AddCommGroup (P n)] [∀ n, Module S (P n)]
variable (π : ∀ n, H →ₗ[R] Q n) (ρ : ∀ n, K →ₗ[S] P n)
variable (hpowπ : ∀ n, I ^ n • (⊤ : Submodule R H) ≤ LinearMap.ker (π n))
variable (hpowρ : ∀ n, J ^ n • (⊤ : Submodule S K) ≤ LinearMap.ker (ρ n))
variable (f : H →ₛₗ[σ] K) (g : ∀ n, Q n →ₛₗ[σ] P n)
variable (hmem : ∀ n, I ^ n • (⊤ : Submodule R H) ≤
  (J ^ n • (⊤ : Submodule S K)).comap f)
variable (hproj : ∀ n, (g n).comp (π n) = (ρ n).comp f)
include hproj

/-- 半線形な射影の可換式は、各イデアル冪による剰余類にも降りる。 -/
theorem adicProjectionQuotientMap_semilinear_naturality (n : ℕ) :
    (g n).comp (adicProjectionQuotientMap I π hpowπ n) =
      (adicProjectionQuotientMap J ρ hpowρ n).comp
        (adicSemilinearQuotientMap I J f hmem n) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (I ^ n • (⊤ : Submodule R H)) x (fun m ↦ ?_)
  exact DFunLike.congr_fun (hproj n) m

variable (t : ∀ i j : ℕ, j ≤ i → Q i →ₗ[R] Q j)
variable (s : ∀ i j : ℕ, j ≤ i → P i →ₗ[S] P j)
variable (hπ : ∀ i j (h : j ≤ i), (t i j h).comp (π i) = π j)
variable (hρ : ∀ i j (h : j ≤ i), (s i j h).comp (ρ i) = ρ j)
variable (hg : ∀ i j (h : j ≤ i), (s i j h).comp (g i) = (g j).comp (t i j h))

/-- 完備化から互換族への標準写像は、係数環を変える半線形写像と可換。 -/
theorem adicProjectionCompletionMap_semilinear_naturality_apply (a : AdicCompletion I H) :
    compatibleSemilinearFamiliesMap σ t s g hg (adicProjectionCompletionMap I π hpowπ t hπ a) =
      adicProjectionCompletionMap J ρ hpowρ s hρ (adicSemilinearCompletionMap I J f hmem a) := by
  apply Subtype.ext
  funext n
  change g n (adicProjectionQuotientMap I π hpowπ n (a.val n)) =
    adicProjectionQuotientMap J ρ hpowρ n (adicSemilinearQuotientMap I J f hmem n (a.val n))
  exact DFunLike.congr_fun (adicProjectionQuotientMap_semilinear_naturality
    I J π ρ hpowπ hpowρ f g hmem hproj n) (a.val n)

end SerrePositivity.AlgebraicGeometry
