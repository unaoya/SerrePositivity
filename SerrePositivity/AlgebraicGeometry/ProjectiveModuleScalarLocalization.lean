module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：加群の分母を係数環へ写した局所化を、元の係数環の局所化と比較する。
方針：Mathlib の restrictScalars_powers と局所化の普遍性による同値を使う。
規約：環ではなく任意の加群を扱い、比較は共通の基底環上で線形とする。
使われ方：Rees 加群の多項式環の係数を変え、各標準開の局所化を比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

variable {R P Q M : Type*} [CommRing R] [CommRing P] [CommRing Q]
variable [Algebra R P] [Algebra P Q] [Algebra R Q] [IsScalarTower R P Q]
variable [AddCommGroup M] [Module R M] [Module P M] [Module Q M]
variable [IsScalarTower R P M] [IsScalarTower R Q M] [IsScalarTower P Q M]

/-- 分母の冪を係数環へ写す。 -/
def projectiveModuleScalarDenominator (f : P) (s : Submonoid.powers f) :
    Submonoid.powers (algebraMap P Q f) :=
  ⟨algebraMap P Q s.val, by
    obtain ⟨n, hn⟩ := s.property
    refine ⟨n, ?_⟩
    change f ^ n = s.val at hn
    change (algebraMap P Q f) ^ n = algebraMap P Q s.val
    rw [← map_pow, hn]⟩

/-- 係数環へ写した分母の局所化との線形同値。 -/
def projectiveModuleScalarLocalizationLinearEquiv (f : P) :
    LocalizedModule (Submonoid.powers f) M ≃ₗ[R]
      LocalizedModule (Submonoid.powers (algebraMap P Q f)) M := by
  let q := LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap P Q f)) M
  letI := IsLocalizedModule.restrictScalars_powers f q
  exact (IsLocalizedModule.iso (Submonoid.powers f) (q.restrictScalars P)).restrictScalars R

/-- 局所化の比較は、分子を保ち、分母だけを係数環へ写す。 -/
theorem projectiveModuleScalarLocalizationLinearEquiv_mk (f : P) (m : M)
    (s : Submonoid.powers f) :
    projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) f (LocalizedModule.mk m s) =
      LocalizedModule.mk m (projectiveModuleScalarDenominator (Q := Q) f s) := by
  let q := LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap P Q f)) M
  letI := IsLocalizedModule.restrictScalars_powers f q
  change IsLocalizedModule.iso (Submonoid.powers f) (q.restrictScalars P)
    (LocalizedModule.mk m s) = _
  apply (IsLocalizedModule.iso (Submonoid.powers f) (q.restrictScalars P)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  symm
  apply IsLocalizedModule.iso_symm_apply'
  change (s.val : P) • LocalizedModule.mk m (projectiveModuleScalarDenominator (Q := Q) f s) =
    LocalizedModule.mk m 1
  rw [LocalizedModule.smul'_mk]
  have hsm : s.val • m = (projectiveModuleScalarDenominator (Q := Q) f s).val • m :=
    (algebraMap_smul Q s.val m).symm
  rw [hsm]
  exact LocalizedModule.mk_cancel _ _

/-- 比較は分母一の分子を保つ。 -/
@[simp]
theorem projectiveModuleScalarLocalizationLinearEquiv_mk_one (f : P) (m : M) :
    projectiveModuleScalarLocalizationLinearEquiv (R := R) (Q := Q) f
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
        LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap P Q f)) M m := by
  let q := LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap P Q f)) M
  letI := IsLocalizedModule.restrictScalars_powers f q
  change IsLocalizedModule.iso (Submonoid.powers f) (q.restrictScalars P)
    (LocalizedModule.mk m 1) = q m
  exact IsLocalizedModule.iso_mk_one _ _ _

end SerrePositivity.AlgebraicGeometry
