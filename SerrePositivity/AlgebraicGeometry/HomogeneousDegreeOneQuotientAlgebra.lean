module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneQuotient
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartAlgebra

/-!
概要：脱斉次化の同型と、既存の標準開の係数環の作用との整合性。
方針：局所化への単射で係数の像を照合し、同じ環同型を代数同型に束ねる。
規約：既存の projectiveHomogeneousAwayAlgebra を使う。
使われ方：Segre チャートの基底上のテンソル積比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)
local instance : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f

/-- 正規化は既存の標準開の代数構造の下で係数を保つ。 -/
theorem homogeneousDegreeOneNormalize_algebraMap (r : R) :
    homogeneousDegreeOneNormalize G hf (algebraMap R A r) =
      algebraMap R (HomogeneousLocalization.Away G f) r := by
  rw [homogeneousDegreeOneNormalize_of_mem G hf _ (SetLike.algebraMap_mem_graded G r)]
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  have hs : (algebraMap R (HomogeneousLocalization.Away G f) r).val =
      r • (1 : Localization.Away f) := by
    rw [Algebra.algebraMap_eq_smul_one, HomogeneousLocalization.val_smul,
      HomogeneousLocalization.val_one]
  rw [hs, HomogeneousLocalization.Away.val_mk]
  simp only [pow_zero]
  change Localization.mk (algebraMap R A r) 1 = r • (1 : Localization.Away f)
  rw [Localization.mk_one_eq_algebraMap]
  simp only [Algebra.smul_def, mul_one]
  exact (IsScalarTower.algebraMap_apply R A (Localization.Away f) r).symm

/-- 脱斉次化の商と斉次局所化の同じ同型を、基底環上の代数同型にする。 -/
def homogeneousDegreeOneQuotientAlgEquiv :
    (A ⧸ Ideal.span ({f - 1} : Set A)) ≃ₐ[R] HomogeneousLocalization.Away G f where
  __ := homogeneousDegreeOneQuotientEquiv G hf
  commutes' r := by
    change homogeneousDegreeOneNormalize G hf (algebraMap R A r) = _
    exact homogeneousDegreeOneNormalize_algebraMap G hf r

/-- 代数同型の環同型への忘却は、構成した同じ環同型。 -/
theorem homogeneousDegreeOneQuotientAlgEquiv_toRingEquiv :
    (homogeneousDegreeOneQuotientAlgEquiv G hf).toRingEquiv =
      homogeneousDegreeOneQuotientEquiv G hf := rfl

end SerrePositivity.AlgebraicGeometry
