module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotient

/-!
概要：閉厚化の実際の商加群の間の I 進遷移を作る。
方針：イデアルの冪の包含による商写像を使う。
規約：第 i 段から第 j 段への遷移には j≤i を要求する。
使われ方：閉厚化の Čech 長完全列の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R)
local instance quotientTransitionModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n

/-- 閉厚化の実際の商加群の間の、多項式環上線形な I 進遷移。 -/
def reesAdicProjectiveQuotientTransition (i j : ℕ) (h : j ≤ i) :
    reesAdicProjectiveQuotient (ι := ι) (M := M) I i →ₗ[MvPolynomial ι R]
      reesAdicProjectiveQuotient (ι := ι) (M := M) I j :=
  (((I.map (algebraMap R (MvPolynomial ι R))) ^ i •
    (⊤ : Submodule (MvPolynomial ι R) M))).mapQ
    (((I.map (algebraMap R (MvPolynomial ι R))) ^ j •
      (⊤ : Submodule (MvPolynomial ι R) M))) LinearMap.id
    (reesAdicProjectiveSubmodule_antitone (ι := ι) (M := M) I h)

/-- 商への射影は、閉厚化の I 進遷移と可換。 -/
theorem reesAdicProjectiveQuotientTransition_projection (i j : ℕ) (h : j ≤ i) :
    (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h).comp
      (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I i) =
    reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I j := by
  ext m
  rfl

/-- 閉厚化の商の遷移は、Proj 次数を保つ。 -/
theorem reesAdicProjectiveQuotientTransition_preservesPiece
    (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
    (i j : ℕ) (h : j ≤ i) (d : ℕ)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := M) I i)
    (hx : x ∈ reesAdicProjectiveQuotientPiece (ι := ι) I G i d) :
    reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h x ∈
      reesAdicProjectiveQuotientPiece (ι := ι) I G j d := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨m, hm, rfl⟩

end SerrePositivity.AlgebraicGeometry
