module

public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarLocalization

/-!
概要：加群と環の局所化の比較を、分母の冪で書いた分数に適用する。
方針：既存の分母の像の公式を mk' の表示にそろえる。
規約：分母の指数を明示し、部分型の証明の違いは無視する。
使われ方：厚化 Frobenius の分子・分母の冪の式を加群の局所化へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {R P A : Type*} [CommRing R] [CommRing P] [CommRing A]
variable [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]

/-- 加群の局所化の分母 f^n を、環の局所化の分母 (algebraMap f)^n へ移す。 -/
theorem projectiveScalarLocalizationLinearEquiv_fraction (f : P) (x : A) (n : ℕ) :
    projectiveScalarLocalizationLinearEquiv (R := R) f
      (LocalizedModule.mk x (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)) =
    IsLocalization.mk' (Localization.Away (algebraMap P A f)) x
      (⟨(algebraMap P A f) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (algebraMap P A f)) := by
  rw [projectiveScalarLocalizationLinearEquiv_mk, Localization.mk_eq_mk']
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap P A) f n

end SerrePositivity.AlgebraicGeometry
