module

public import SerrePositivity.AlgebraicGeometry.AwayPowerMapSemilinear
public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarLocalizationFraction

/-!
概要：分母を冪に送る環準同型を、標準開の加群局所化の半線形写像へ移す。
方針：Away 局所化で延長した写像を、既存のスカラー局所化の比較で共役する。
規約：分子は元の環準同型、分母の指数は k 倍。
使われ方：厚化 Frobenius の指定次数部分への制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R P A B : Type u} [CommRing R] [CommRing P] [CommRing A] [CommRing B]
variable [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable [Algebra R B] [Algebra P B] [IsScalarTower R P B]
variable (ρ : R →+* R) (φ : A →+* B) (s : P) (k : ℕ)
variable (hd : φ (algebraMap P A s) = (algebraMap P B s) ^ k)
variable (hs : ∀ r, φ (algebraMap R A r) = algebraMap R B (ρ r))

/-- 標準開の加群局所化の間で、分母を冪に送る実際の半線形写像。 -/
def projectiveLocalizedPowerMap :
    LocalizedModule (Submonoid.powers s) A →ₛₗ[ρ] LocalizedModule (Submonoid.powers s) B :=
  (projectiveScalarLocalizationLinearEquiv (R := R) (S := B) s).symm.toLinearMap.comp
    ((awayPowerMapSemilinear ρ φ (algebraMap P A s) (algebraMap P B s) k hd hs).comp
      (projectiveScalarLocalizationLinearEquiv (R := R) (S := A) s).toLinearMap)

/-- 加群局所化の分数の像は、分子 φ(x)、分母 s^(k*n)。 -/
theorem projectiveLocalizedPowerMap_fraction (x : A) (n : ℕ) :
    projectiveLocalizedPowerMap ρ φ s k hd hs
      (LocalizedModule.mk x (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s)) =
    LocalizedModule.mk (φ x) (⟨s ^ (k * n), ⟨k * n, rfl⟩⟩ : Submonoid.powers s) := by
  apply (projectiveScalarLocalizationLinearEquiv (R := R) (S := B) s).injective
  change (projectiveScalarLocalizationLinearEquiv (R := R) (S := B) s)
    ((projectiveScalarLocalizationLinearEquiv (R := R) (S := B) s).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change awayPowerMap φ (algebraMap P A s) (algebraMap P B s) k hd
    (projectiveScalarLocalizationLinearEquiv (R := R) (S := A) s _) = _
  rw [projectiveScalarLocalizationLinearEquiv_fraction,
    projectiveScalarLocalizationLinearEquiv_fraction]
  exact awayPowerMap_fraction φ (algebraMap P A s) (algebraMap P B s) k hd x n

end SerrePositivity.AlgebraicGeometry
