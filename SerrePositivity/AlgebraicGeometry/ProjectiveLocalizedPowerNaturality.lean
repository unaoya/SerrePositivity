module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerMap

/-!
概要：分母を冪に送る局所化の写像と、係数の線形写像の可換四角形。
方針：元の環の可換四角形を分数の分子に適用する。
規約：縦の二つの写像は P 線形、横は同じ指数 k の半線形写像。
使われ方：閉厚化の射影・遷移と反復 Frobenius の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R P A B C D : Type u}
variable [CommRing R] [CommRing P] [CommRing A] [CommRing B]
variable [CommRing C] [CommRing D] [Algebra R P]
variable [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable [Algebra R B] [Algebra P B] [IsScalarTower R P B]
variable [Algebra R C] [Algebra P C] [IsScalarTower R P C]
variable [Algebra R D] [Algebra P D] [IsScalarTower R P D]
variable (ρ : R →+* R) (φ : A →+* B) (ψ : C →+* D) (s : P) (k : ℕ)
variable (hφ : φ (algebraMap P A s) = (algebraMap P B s) ^ k)
variable (hψ : ψ (algebraMap P C s) = (algebraMap P D s) ^ k)
variable (hsφ : ∀ r, φ (algebraMap R A r) = algebraMap R B (ρ r))
variable (hsψ : ∀ r, ψ (algebraMap R C r) = algebraMap R D (ρ r))

/-- 係数の可換四角形は、分母を同じ冪に送る局所化の可換四角形を与える。 -/
theorem projectiveLocalizedPowerMap_naturality
    (f : A →ₗ[P] C) (g : B →ₗ[P] D) (h : ∀ a, ψ (f a) = g (φ a))
    (z : LocalizedModule (Submonoid.powers s) A) :
    projectiveLocalizedPowerMap ρ ψ s k hψ hsψ
      (IsLocalizedModule.map (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) A)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) C) f z) =
    IsLocalizedModule.map (Submonoid.powers s)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) B)
      (LocalizedModule.mkLinearMap (Submonoid.powers s) D) g
      (projectiveLocalizedPowerMap ρ φ s k hφ hsφ z) := by
  induction z using LocalizedModule.induction_on with
  | _ x t =>
    obtain ⟨t, n, rfl⟩ := t
    change projectiveLocalizedPowerMap ρ ψ s k hψ hsψ
      (IsLocalizedModule.map (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) A)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) C) f
        (LocalizedModule.mk x (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s))) =
      IsLocalizedModule.map (Submonoid.powers s)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) B)
        (LocalizedModule.mkLinearMap (Submonoid.powers s) D) g
        (projectiveLocalizedPowerMap ρ φ s k hφ hsφ
          (LocalizedModule.mk x (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s)))
    rw [IsLocalizedModule.map_LocalizedModules]
    rw [projectiveLocalizedPowerMap_fraction, projectiveLocalizedPowerMap_fraction,
      IsLocalizedModule.map_LocalizedModules, h]

end SerrePositivity.AlgebraicGeometry
