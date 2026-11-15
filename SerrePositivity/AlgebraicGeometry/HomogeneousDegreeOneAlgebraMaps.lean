module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneQuotientAlgebra

/-!
概要：脱斉次化と特殊化を既存の係数環上の代数写像に束ねる。
方針：正規化の係数保存と、特殊化との合成の式を使う。
規約：同じ環写像と projectiveHomogeneousAwayAlgebra を保持する。
使われ方：Segre 標準開の二因子への写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
variable [Algebra R A] [Algebra R C]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)
local instance : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f

/-- 同じ脱斉次化の環写像を、係数環上の代数写像に束ねる。 -/
def homogeneousDegreeOneNormalizeAlgHom : A →ₐ[R] HomogeneousLocalization.Away G f where
  __ := homogeneousDegreeOneNormalize G hf
  commutes' := homogeneousDegreeOneNormalize_algebraMap G hf

/-- 同じ特殊化の環写像を、係数環上の代数写像に束ねる。 -/
def homogeneousDegreeOneSpecializeAlgHom (φ : A →ₐ[R] C) (hφ : φ f = 1) :
    HomogeneousLocalization.Away G f →ₐ[R] C where
  __ := homogeneousDegreeOneSpecialize G φ.toRingHom hφ
  commutes' r := by
    change homogeneousDegreeOneSpecialize G φ.toRingHom hφ
      (algebraMap R (HomogeneousLocalization.Away G f) r) = algebraMap R C r
    rw [← homogeneousDegreeOneNormalize_algebraMap G hf r,
      homogeneousDegreeOneSpecialize_normalize G hf φ.toRingHom hφ]
    exact φ.commutes r

/-- 正規化の代数写像は同じ環写像を持つ。 -/
theorem homogeneousDegreeOneNormalizeAlgHom_toRingHom :
    (homogeneousDegreeOneNormalizeAlgHom G hf).toRingHom =
      homogeneousDegreeOneNormalize G hf := rfl

/-- 特殊化の代数写像は同じ環写像を持つ。 -/
theorem homogeneousDegreeOneSpecializeAlgHom_toRingHom (φ : A →ₐ[R] C) (hφ : φ f = 1) :
    (homogeneousDegreeOneSpecializeAlgHom G hf φ hφ).toRingHom =
      homogeneousDegreeOneSpecialize G φ.toRingHom hφ := rfl

end SerrePositivity.AlgebraicGeometry
