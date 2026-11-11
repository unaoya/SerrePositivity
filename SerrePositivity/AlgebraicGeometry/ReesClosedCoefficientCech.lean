module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatPolynomialCoefficientChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedFiniteness

/-!
概要：閉厚化の標準開 Čech 図式を、商環 R/J 上の表示と比較する。
方針：実際の商加群の二つの多項式作用と次数成分を、係数変更の比較へ渡す。
規約：非平坦な閉厚化であり、コホモロジーとテンソル積の交換は仮定しない。
使われ方：Stacks 30.20.5 の形式関数に対応する Čech 版の係数表示。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
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
local instance : IsScalarTower R (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_base_scalarTower (ι := ι) J
local instance : IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) J
local instance : Algebra (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J)) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).toAlgebra
local instance : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_scalarTower (ι := ι) J

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
    (reesClosedCoefficientPiece (ι := ι) J G) :=
  reesClosedCoefficientPieceGradedSMul (ι := ι) J G
local instance : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
    (fun n ↦ (reesClosedCoefficientPiece (ι := ι) J G n).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1

local instance : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1

variable [Fintype ι]
section Comparison
variable [DecidableEq ι]

/-- 実際の閉厚化の R 上の標準開図式と、R/J 上の表示の係数制限の同型。 -/
def reesClosedCoefficientChartIso (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d ≅
      projectiveNatGradedModuleChartDiagram (R := R ⧸ J) (ι := ι)
        (reesClosedCoefficientPiece (ι := ι) J G) d ⋙
          ModuleCat.restrictScalars (Ideal.Quotient.mk J) :=
  projectiveNatPolynomialCoefficientChangeChartIso
    (R := R) (B := R ⧸ J) (ι := ι) (reesClosedCoefficientPiece (ι := ι) J G) d

/-- 閉厚化の Čech コホモロジーは、商環上の同じ標準開計算の係数制限と一致する。
原典 Stacks 30.20.5 の Hⁱ の形式関数へ渡す閉厚化の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedCoefficientCechHomologyIso (d : ℤ) (q : ℕ) :=
  projectiveNatPolynomialCoefficientChangeCechHomologyIso
    (R := R) (B := R ⧸ J) (ι := ι) (reesClosedCoefficientPiece (ι := ι) J G) d q

end Comparison

variable [LinearOrder ι] [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) M]

/-- 商環 R/J 上で表示した閉厚化の標準開 Čech コホモロジーは有限生成。
原典 Stacks 30.19.2 の Hⁱ の射影有限性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCoefficientCechHomology_finite (d : ℤ) (q : ℕ) :
    Module.Finite (R ⧸ J) ((fullCechComplex
      (projectiveNatGradedModuleChartDiagram (R := R ⧸ J) (ι := ι)
        (reesClosedCoefficientPiece (ι := ι) J G) d)).homology q) := by
  let N := ((fullCechComplex
    (projectiveNatGradedModuleChartDiagram (R := R ⧸ J) (ι := ι)
      (reesClosedCoefficientPiece (ι := ι) J G) d)).homology q)
  letI : Module R N := Module.compHom N (Ideal.Quotient.mk J)
  letI : IsScalarTower R (R ⧸ J) N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  letI := reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1
  letI : Module.Finite (MvPolynomial ι R)
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
    inferInstanceAs (Module.Finite (MvPolynomial ι R)
      (M ⧸ ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
        (⊤ : Submodule (MvPolynomial ι R) M))))
  letI := projectiveNatGradedFullCechHomology_finite (ι := ι)
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q
  let e : ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d)).homology q) ≃ₗ[R] N :=
    (reesClosedCoefficientCechHomologyIso (ι := ι) J G d q).toLinearEquiv
  letI : Module.Finite R N := Module.Finite.equiv e
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ J) N

end SerrePositivity.AlgebraicGeometry
