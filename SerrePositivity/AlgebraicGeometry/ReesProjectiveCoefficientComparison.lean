module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatPolynomialCoefficientChange
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechDirectSum
public import SerrePositivity.AlgebraicGeometry.ReesPolynomialCoefficientTowers
public import SerrePositivity.AlgebraicGeometry.ReesProjectiveFiniteness

/-!
概要：Rees 環上の多項式環の Čech コホモロジーを、各 IⁿM の直和へ接続する。
方針：係数変更の自然数次数の比較を Rees 加群へ特殊化し、P 上の直和比較と合成する。
規約：この同型は基底環 R 上のもの。直和の Rees 次数に対する作用は別に追跡する。
使われ方：原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesCoefficientCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesCoefficientCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesCoefficientCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesCoefficientCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesCoefficientCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesCoefficientCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesCoefficientCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesCoefficientCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesCoefficientCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesCoefficientCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesCoefficientCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

local instance reesCoefficientCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra (ι := ι) I
local instance reesCoefficientCechRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra_scalarTower (ι := ι) I
local instance reesCoefficientCechModule :
    Module (MvPolynomial ι (reesAlgebra I)) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)
local instance reesCoefficientCechSourceTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_source_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesCoefficientCechBaseTower :
    IsScalarTower R (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_base_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesCoefficientCechReesTower :
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesCoefficientCechBaseGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun n ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G n).restrictScalars R) :=
  reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
local instance reesCoefficientCechReesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) :=
  reesProjectivePolynomialGradedSMul (R := R) (M := M) (ι := ι) I G

/-- P 上と B[X] 上の Rees 加群の標準開の図式を、R に係数制限して比較する。 -/
def reesAdicProjectiveCoefficientChartIso (d : ℤ) :=
  projectiveNatPolynomialCoefficientChangeChartIso
    (R := R) (B := reesAlgebra I) (ι := ι)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) d

/-- Rees 加群の二つの多項式環での Čech コホモロジーを R 上で比較する。
原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveCoefficientCechHomologyIso (d : ℤ) (q : ℕ) :=
  projectiveNatPolynomialCoefficientChangeCechHomologyIso
    (R := R) (B := reesAlgebra I) (ι := ι)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) d q

/-- B[X] 上の Rees 加群の Čech コホモロジーを R に制限したものと、各 IⁿM の直和との同型。
原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveCechHomologyDirectSumIso (d : ℤ) (q : ℕ) :=
  (reesAdicProjectiveCoefficientCechHomologyIso (R := R) (M := M) (ι := ι) I G d q).symm ≪≫
    reesAdicProjectiveBaseCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q

end SerrePositivity.AlgebraicGeometry
