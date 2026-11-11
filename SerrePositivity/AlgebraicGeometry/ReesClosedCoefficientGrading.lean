module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientTower
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousCoefficientLift

/-!
概要：閉厚化の Proj 次数成分を商環 R/J 上の部分加群として扱う。
方針：商環の代表で部分加群の閉性を示し、斉次持ち上げで多項式作用を降ろす。
規約：次数成分の台は元の R 上の商次数成分と同じ。
使われ方：閉厚化の標準開を (R/J)[X] で表示するための入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (J : Ideal R)

local instance : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) J 1
local instance : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) J 1
local instance : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J
local instance : IsScalarTower R (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficient_scalarTower (ι := ι) J
local instance : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- 閉厚化の次数成分を、商環上の部分加群として表したもの。 -/
def reesClosedCoefficientPiece (d : ℕ) :
    Submodule (R ⧸ J) (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) where
  toAddSubmonoid := (reesAdicProjectiveQuotientPiece (ι := ι) J G 1 d).toAddSubmonoid
  smul_mem' := by
    intro b x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [reesClosedCoefficient_mk_smul]
    exact (reesAdicProjectiveQuotientPiece (ι := ι) J G 1 d).smul_mem r hx

/-- 商係数の次数成分を R へ制限すると、元の次数成分そのものになる。 -/
theorem reesClosedCoefficientPiece_restrictScalars (d : ℕ) :
    (reesClosedCoefficientPiece (ι := ι) J G d).restrictScalars R =
      reesAdicProjectiveQuotientPiece (ι := ι) J G 1 d := rfl

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 商係数の斉次多項式作用は、閉厚化の Proj 次数を保つ。 -/
theorem reesClosedCoefficientPieceGradedSMul :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
      (reesClosedCoefficientPiece (ι := ι) J G) := by
  letI := reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨a, ha, rfl⟩ := projectiveHomogeneousCoefficientLift (Ideal.Quotient.mk J)
    (Ideal.Quotient.mk_surjective) p hp
  rw [reesClosedPolynomialCoefficient_map_smul]
  exact SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R)
    (B := reesAdicProjectiveQuotientPiece (ι := ι) J G 1) ha hx

end SerrePositivity.AlgebraicGeometry
