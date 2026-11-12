module

public import SerrePositivity.AlgebraicGeometry.ReesAdicGradedLocalizedDirectSum
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartDirectSum

/-!
概要：Rees 加群の P 上の標準開 Čech コホモロジーを、各 IⁿM の直和と比較する。
方針：Rees 同値で分子の次数を対応させ、自然数次数の標準開の直和比較へ渡す。
規約：この比較は基底環 R 上で線形とする。
使われ方：原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の Rees 比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesBaseCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesBaseCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesBaseCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesBaseCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesBaseCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesBaseCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesBaseCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesBaseCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesBaseCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesBaseCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesBaseCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

/-- Rees 加群の Proj 次数を、元の基底環に制限したもの。 -/
abbrev reesAdicProjectiveBaseGrade (d : ℕ) :
    Submodule R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G d).restrictScalars R

local instance reesBaseCechPieceGradedSMul (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (R := R) (M := M) (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (R := R) (M := M) (ι := ι) I G n

/-- 元の多項式環の作用も、Rees 加群の Proj 次数を保つ次数付き作用。 -/
theorem reesAdicProjectiveBaseGradedSMul :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveBaseGrade (ι := ι) I G) := by
  exact projectiveNatGradedSMul_of_directSumLinearEquiv
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun n ↦ reesAdicProjectivePiece (R := R) (M := M) (ι := ι) I G n)
    (reesAdicProjectiveBaseGrade (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (fun d x ↦ reesAdicDirectSumPolynomialLinearEquiv_projective_mem
      (R := R) (M := M) (ι := ι) I G d x)

/-- P 上の Rees 加群の標準開の係数図式と、各 IⁿM の係数図式の直和との同型。 -/
def reesAdicProjectiveBaseChartDirectSumIso (d : ℤ) :=
  letI := reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
  projectiveNatGradedModuleChartDirectSumIso
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun n ↦ reesAdicProjectivePiece (R := R) (M := M) (ι := ι) I G n)
    (reesAdicProjectiveBaseGrade (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (fun k x ↦ reesAdicDirectSumPolynomialLinearEquiv_projective_mem
      (R := R) (M := M) (ι := ι) I G k x) d

/-- P 上の Rees 加群の Čech コホモロジーと、各 IⁿM の同じコホモロジーの直和との R 線形同型。
原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveBaseCechHomologyDirectSumIso (d : ℤ) (q : ℕ) :=
  letI := reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
  projectiveNatGradedModuleChartDirectSumCechHomologyIso
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun n ↦ reesAdicProjectivePiece (R := R) (M := M) (ι := ι) I G n)
    (reesAdicProjectiveBaseGrade (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (fun k x ↦ reesAdicDirectSumPolynomialLinearEquiv_projective_mem
      (R := R) (M := M) (ι := ι) I G k x) d q

end SerrePositivity.AlgebraicGeometry
