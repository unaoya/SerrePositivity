module

public import SerrePositivity.AlgebraicGeometry.ReesIteratedClosedGrading
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotientTransition

/-!
概要：一重の商 M/(JM+IⁿM) の遷移と、二重閉厚化の比較の自然性。
方針：分母の和の包含から商写像を作り、代表で可換性を示す。
規約：全写像を多項式環上線形に扱う。
使われ方：閉厚化の Čech 比較を、各段の同型から互換族の同型へ送る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I J : Ideal R)
local instance iteratedTransitionModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) J 1
local instance iteratedTransitionTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) J 1
local instance iteratedTransitionQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n

/-- 一重の商 M/(JM+IⁱM) から M/(JM+IʲM) への遷移。 -/
def reesIteratedClosedSumTransition (i j : ℕ) (h : j ≤ i) :
    M ⧸ (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
        reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I i) →ₗ[MvPolynomial ι R]
      M ⧸ (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
        reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I j) :=
  (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
    reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I i).mapQ
    (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
      reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I j) LinearMap.id
    (sup_le_sup le_rfl (Submodule.smul_mono
      (Ideal.pow_le_pow_right (I := I.map (algebraMap R (MvPolynomial ι R))) h) le_rfl))

/-- 二重閉厚化から一重の商への同型は、実際の遷移と可換。 -/
theorem reesIteratedClosedQuotientLinearEquiv_transition (i j : ℕ) (h : j ≤ i) :
    (reesIteratedClosedSumTransition (ι := ι) (M := M) I J i j h).comp
      (reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J i).toLinearMap =
    (reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J j).toLinearMap.comp
      (reesAdicProjectiveQuotientTransition (ι := ι)
        (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I i j h) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι)
    (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I i x
  obtain ⟨m, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) J 1 y
  rfl

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 一重の商の遷移は、元の Proj 次数を保つ。 -/
theorem reesIteratedClosedSumTransition_preservesPiece
    (i j : ℕ) (h : j ≤ i) (d : ℕ)
    (x : M ⧸ (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
      reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I i))
    (hx : x ∈ reesIteratedClosedSumPiece (ι := ι) I J G i d) :
    reesIteratedClosedSumTransition (ι := ι) (M := M) I J i j h x ∈
      reesIteratedClosedSumPiece (ι := ι) I J G j d := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨m, hm, rfl⟩

end SerrePositivity.AlgebraicGeometry
