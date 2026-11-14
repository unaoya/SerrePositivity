module

public import SerrePositivity.AlgebraicGeometry.ProjectiveRingQuotientGrading
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.Subquotient
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
概要：同次イデアルによる実際の環の商に、既存の次数成分の直和分解を供給する。
方針：HilbertSerre の商加群の内部直和を、係数制限の商の同型で実際の環の商へ移す。
規約：projectiveRingQuotientGrade の定義と既存の Rees の宣言を変えない。
使われ方：G3 の Segre 座標環の商と 2f の射影入力の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (J : Ideal A) (G : ℕ → Submodule R A) [GradedRing G]
variable (hJ : J.IsHomogeneous G)
include hJ

/-- 同次イデアルの実際の環の商の既存の次数成分は内部直和。 -/
theorem homogeneousIdealQuotientGrade_isInternal :
    DirectSum.IsInternal (projectiveRingQuotientGrade J G) := by
  let S := J.restrictScalars R
  have hS : S.IsHomogeneous G := hJ
  let H := SerrePositivity.HilbertSerre.quotientGrade G S
  let e := Submodule.Quotient.restrictScalarsEquiv R J
  have hH := SerrePositivity.HilbertSerre.isInternal_quotientGrade G S hS
  have he : (fun j ↦ (H j).map e.toLinearMap) = projectiveRingQuotientGrade J G := by
    funext j
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Submodule.Quotient.mk a, ⟨a, ha, rfl⟩, rfl⟩
  rw [← he]
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact e.toLinearMap.iSupIndep_map e.injective hH.submodule_iSupIndep
  · rw [← Submodule.map_iSup, hH.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective

/-- 同じ商の積と内部直和を合わせた次数付き環。 -/
@[instance_reducible]
def homogeneousIdealQuotientGradedRing : GradedRing (projectiveRingQuotientGrade J G) where
  toDecomposition := (homogeneousIdealQuotientGrade_isInternal J G hJ).chooseDecomposition
  toGradedMonoid := inferInstance

end SerrePositivity.AlgebraicGeometry
