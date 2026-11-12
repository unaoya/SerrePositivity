module

public import SerrePositivity.AlgebraicGeometry.ReesClosedTensorComparison
public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedEquiv

/-!
概要：R/J にテンソルした加群の標準開と、既存の閉厚化の係数図式を照合する。
方針：実際の多項式加群の同型と次数成分の一致を、既存の標準開の関手へ送る。
規約：R→R/J の平坦性は仮定しない。元の H とテンソル積の交換は主張しない。
使われ方：閉厚化の商係数表示を、基底変更後の実際の標準開と同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (J : Ideal R)
local instance reesClosedTensorChartSourceCoefficientModule :
    Module (R ⧸ J) (M ⊗[R] (R ⧸ J)) := tensorRightCoefficientModule
local instance reesClosedTensorChartSourcePolynomialModule :
    Module (MvPolynomial ι (R ⧸ J)) (M ⊗[R] (R ⧸ J)) := projectiveTensorPolynomialModule
local instance reesClosedTensorChartSourcePolynomialTower :
    IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J)) (M ⊗[R] (R ⧸ J)) :=
  projectiveTensorPolynomial_coefficient_scalarTower
local instance reesClosedTensorChartTargetCoefficientModule : Module (R ⧸ J)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedCoefficientModule (ι := ι) J
local instance reesClosedTensorChartTargetPolynomialModule : Module (MvPolynomial ι (R ⧸ J))
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficientModule (ι := ι) J
local instance reesClosedTensorChartTargetPolynomialTower :
    IsScalarTower (R ⧸ J) (MvPolynomial ι (R ⧸ J))
      (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesClosedPolynomialCoefficient_quotient_scalarTower (ι := ι) J

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- 商とのテンソル比較は、元の次数成分を両方向で対応させる。 -/
theorem reesClosedTensorPiece_mem_iff (j : ℕ) (x : M ⊗[R] (R ⧸ J)) :
    reesClosedTensorPolynomialEquiv (ι := ι) J x ∈ reesClosedCoefficientPiece (ι := ι) J G j ↔
      x ∈ projectiveTensorPiece (B := R ⧸ J) G j := by
  change reesClosedTensorCoefficientEquiv (ι := ι) J x ∈ _ ↔ _
  rw [← reesClosedTensorPiece_map_eq (ι := ι) J G j, Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply]

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance reesClosedTensorChartSourceGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
      (projectiveTensorPiece (B := R ⧸ J) G) := projectiveTensorPiece_gradedSMul (ι := ι) G
local instance reesClosedTensorChartTargetGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (R ⧸ J))
      (reesClosedCoefficientPiece (ι := ι) J G) :=
  reesClosedCoefficientPieceGradedSMul (ι := ι) J G

/-- R/J にテンソルした加群の標準開図式と、既存の閉厚化の商係数図式との自然同型。 -/
def reesClosedTensorChartIso (d : ℤ) :
    projectiveTensorGradedModuleChartDiagram (B := R ⧸ J) (ι := ι) G d ≅
      projectiveNatGradedModuleChartDiagram (R := R ⧸ J) (ι := ι)
        (reesClosedCoefficientPiece (ι := ι) J G) d :=
  projectiveNatGradedModuleChartIso (R := R ⧸ J) (ι := ι)
    (projectiveTensorPiece (B := R ⧸ J) G) (reesClosedCoefficientPiece (ι := ι) J G)
    (reesClosedTensorPolynomialEquiv (ι := ι) J)
    (fun j x hx ↦ (reesClosedTensorPiece_mem_iff (ι := ι) J G j x).mpr hx)
    (fun j y hy ↦ (reesClosedTensorPiece_mem_iff (ι := ι) J G j
      ((reesClosedTensorPolynomialEquiv (ι := ι) J).symm y)).mp
        (by simpa only [LinearEquiv.apply_symm_apply] using hy)) d

/-- R/J にテンソルした加群の実際の標準開と、閉厚化の商係数表示の Čech 比較。
原典 Stacks 30.20.4–30.20.5 の Hⁱ の閉厚化・形式関数に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedTensorCechIso (d : ℤ) (q : ℕ) :
    (fullCechComplex
      (projectiveTensorGradedModuleChartDiagram (B := R ⧸ J) (ι := ι) G d)).homology q ≅
      (fullCechComplex (projectiveNatGradedModuleChartDiagram (R := R ⧸ J) (ι := ι)
        (reesClosedCoefficientPiece (ι := ι) J G) d)).homology q :=
  (fullCechComplexFunctor (R := R ⧸ J) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} (R ⧸ J)) (.up ℕ) q).mapIso
      (reesClosedTensorChartIso (ι := ι) J G d)

end SerrePositivity.AlgebraicGeometry
