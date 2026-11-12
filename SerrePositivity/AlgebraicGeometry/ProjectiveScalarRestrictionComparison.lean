module

public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarGradedLocalization

/-!
概要：局所化の係数環の変更は、分母の整除で得る制限と可換。
方針：分数表示に戻し、追加因子の冪の作用を代数準同型で比較する。
規約：代数の中の分母には、係数環の元の像を使う。
使われ方：斉次代数の標準開の図式と、多項式加群の図式を比較する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

variable {R P S : Type*} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]

/-- 係数環を変える局所化の比較は、追加因子を反転する制限と可換。 -/
theorem projectiveScalarModuleAwayLinearEquiv_restriction
    {f g a : P} (ha : g = f * a) (z : LocalizedModule (Submonoid.powers f) S) :
    projectiveScalarModuleAwayLinearEquiv (R := R) (S := S) g
        (projectiveModuleAwayRestriction (M := S) (show f ∣ g from ⟨a, ha⟩) z) =
      projectiveModuleAwayRestriction (M := S)
        (show algebraMap P S f ∣ algebraMap P S g from
          ⟨algebraMap P S a, by rw [ha, map_mul]⟩)
        (projectiveScalarModuleAwayLinearEquiv (R := R) (S := S) f z) := by
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = projDenominator f n := by
      apply Subtype.ext
      exact hn.symm
    rw [hs]
    have himage : algebraMap P S g = algebraMap P S f * algebraMap P S a := by
      rw [ha, map_mul]
    rw [projectiveModuleAwayRestriction_mk ha, projectiveScalarModuleAwayLinearEquiv_mk,
      projectiveScalarModuleAwayLinearEquiv_mk, projectiveModuleAwayRestriction_mk himage]
    congr 1
    simp [Algebra.smul_def, map_pow]

end SerrePositivity.AlgebraicGeometry
