module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：代数を係数環の加群として局所化する操作と、像の元による環局所化を比較する。
方針：分母の部分モノイドを代数準同型で写し、局所化の普遍性を使う。
規約：三つの係数環の作用は scalar tower でそろえる。
使われ方：多項式加群の Čech 計算を斉次商環の Proj の標準開に移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {R P S : Type*} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]

/-- 分母の冪を代数へ写すと、その像の冪全体になる。 -/
theorem projectiveScalarLocalization_denominators (f : P) :
    Algebra.algebraMapSubmonoid S (Submonoid.powers f) =
      Submonoid.powers (algebraMap P S f) :=
  Submonoid.map_powers _ _

/-- 係数環の加群としての局所化を、代数の元の像による環局所化と比較する。 -/
def projectiveScalarLocalizationLinearEquiv (f : P) :
    LocalizedModule (Submonoid.powers f) S ≃ₗ[R]
      Localization.Away (algebraMap P S f) := by
  let T := Localization.Away (algebraMap P S f)
  letI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) T := by
    rw [projectiveScalarLocalization_denominators]
    infer_instance
  exact (IsLocalizedModule.iso (Submonoid.powers f)
    (IsScalarTower.toAlgHom P S T).toLinearMap).restrictScalars R

/-- 局所化の比較は、分子を保ち、分母だけを代数へ写す。 -/
theorem projectiveScalarLocalizationLinearEquiv_mk (f : P) (x : S)
    (s : Submonoid.powers f) :
    projectiveScalarLocalizationLinearEquiv (R := R) (S := S) f (LocalizedModule.mk x s) =
      Localization.mk x ⟨algebraMap P S s.val, by
        obtain ⟨n, hn⟩ := s.property
        change f ^ n = s.val at hn
        exact ⟨n, by
          change (algebraMap P S f) ^ n = algebraMap P S s.val
          rw [← map_pow, hn]⟩⟩ := by
  let T := Localization.Away (algebraMap P S f)
  letI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) T := by
    rw [projectiveScalarLocalization_denominators]
    infer_instance
  change IsLocalizedModule.mk' (IsScalarTower.toAlgHom P S T).toLinearMap x s = _
  rw [← IsLocalization.mk'_algebraMap_eq_mk', Localization.mk_eq_mk']
  exact IsLocalization.eq_mk'_iff_mul_eq.mpr (IsLocalization.mk'_spec T x _)

end SerrePositivity.AlgebraicGeometry
