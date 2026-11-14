module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedPowerMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction

/-!
概要：分母を冪に送る半線形写像は、標準開を狭める制限と可換。
方針：追加因子の冪を分子に掛ける制限の公式を、同じ分数で比較する。
規約：係数環 P のすべての元の像について k 乗との整合性を仮定する。
使われ方：厚化 Frobenius の各項を Čech 係数図式の射にまとめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R P A B : Type u} [CommRing R] [CommRing P] [CommRing A] [CommRing B]
variable [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable [Algebra R B] [Algebra P B] [IsScalarTower R P B]
variable (ρ : R →+* R) (φ : A →+* B) (k : ℕ)
variable (hP : ∀ s, φ (algebraMap P A s) = (algebraMap P B s) ^ k)
variable (hs : ∀ r, φ (algebraMap R A r) = algebraMap R B (ρ r))

/-- 半線形な局所化の写像は、標準開を狭める制限と可換。 -/
theorem projectiveLocalizedPowerMap_restriction {f g a : P} (ha : g = f * a)
    (z : LocalizedModule (Submonoid.powers f) A) :
    projectiveLocalizedPowerMap ρ φ g k (hP g) hs
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩) z) =
    projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
      (projectiveLocalizedPowerMap ρ φ f k (hP f) hs z) := by
  have hfrac (t : P) (x : A) (n : ℕ) :
      projectiveLocalizedPowerMap ρ φ t k (hP t) hs
        (LocalizedModule.mk x (projDenominator t n)) =
      LocalizedModule.mk (φ x) (projDenominator t (k * n)) :=
    projectiveLocalizedPowerMap_fraction ρ φ t k (hP t) hs x n
  induction z using LocalizedModule.induction_on with
  | _ x s =>
    obtain ⟨s, n, rfl⟩ := s
    change projectiveLocalizedPowerMap ρ φ g k (hP g) hs
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (LocalizedModule.mk x (projDenominator f n))) =
      projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (projectiveLocalizedPowerMap ρ φ f k (hP f) hs
          (LocalizedModule.mk x (projDenominator f n)))
    rw [projectiveModuleAwayRestriction_mk ha, hfrac, hfrac,
      projectiveModuleAwayRestriction_mk ha]
    congr 1
    simp only [Algebra.smul_def, map_mul, map_pow, hP, pow_mul]

end SerrePositivity.AlgebraicGeometry
