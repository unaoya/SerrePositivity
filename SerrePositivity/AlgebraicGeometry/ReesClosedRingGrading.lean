module

public import SerrePositivity.AlgebraicGeometry.ReesClosedRingComparison
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
概要：Rees の閉厚化の直和分解を、実際の環の商の次数成分へ移す。
方針：基底イデアルの作用の斉次性から商の内部直和を得て、実際の環の商へ移す。
規約：環の商の次数成分の定義は変更しない。
使われ方：閉厚化の斉次局所化と Proj の標準開の環の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]

/-- Rees の商の次数成分を環の商への比較で送ると、元の商環の次数成分になる。 -/
theorem reesClosedRingLinearEquiv_map_piece (n j : ℕ) :
    (reesAdicProjectiveQuotientPiece (ι := ι) I G n j).map
        (reesClosedRingLinearEquiv (ι := ι) I n).toLinearMap =
      projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G j := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Submodule.Quotient.mk a, ⟨a, ha, rfl⟩, rfl⟩

/-- 閉厚化の実際の環の次数成分も内部直和をなす。 -/
theorem reesClosedRingGrade_isInternal (n : ℕ) :
    DirectSum.IsInternal (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) := by
  let J := (I ^ n).map (algebraMap R A)
  let S := J.restrictScalars R
  have hS : S.IsHomogeneous G := by
    change (J.restrictScalars R).IsHomogeneous G
    rw [show J.restrictScalars R = I ^ n • (⊤ : Submodule R A) from
      (Ideal.smul_top_eq_map (I ^ n)).symm]
    intro d x hx
    exact Submodule.smul_top_le_comap_smul_top (I ^ n)
      (SerrePositivity.HilbertSerre.gradeProjection G d) hx
  let H := SerrePositivity.HilbertSerre.quotientGrade G S
  let e := Submodule.Quotient.restrictScalarsEquiv R J
  have hH := SerrePositivity.HilbertSerre.isInternal_quotientGrade G S hS
  have he : (fun j ↦ (H j).map e.toLinearMap) =
      projectiveRingQuotientGrade J G := by
    funext j
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Submodule.Quotient.mk a, ⟨a, ha, rfl⟩, rfl⟩
  change DirectSum.IsInternal (projectiveRingQuotientGrade J G)
  rw [← he]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact e.toLinearMap.iSupIndep_map e.injective hH.submodule_iSupIndep
  · rw [← Submodule.map_iSup, hH.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective

/-- 商環の積と、Rees から移した直和分解を合わせた次数付き環構造。 -/
@[instance_reducible]
def reesClosedRingGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) where
  toDecomposition := (reesClosedRingGrade_isInternal I G n).chooseDecomposition
  toGradedMonoid := inferInstance

end SerrePositivity.AlgebraicGeometry
