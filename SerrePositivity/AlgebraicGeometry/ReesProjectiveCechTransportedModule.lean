module

public import SerrePositivity.AlgebraicGeometry.ReesProjectiveCoefficientComparison
public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestrictionTransport

/-!
概要：Rees の Čech 比較に沿って、コホモロジーの直和へ作用と有限性を移す。
方針：B[X] 上のコホモロジーの既存の有限性を、係数制限の同型で移送する。
規約：変数に線形順序を選ぶ。ここでの B 作用は比較で移したもので、次数付き性は別に示す。
使われ方：原典 Stacks 30.20.1 の Hⁱ の直和の有限性に対応する Čech 版の入力。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesTransportedCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesTransportedCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesTransportedCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesTransportedCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesTransportedCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesTransportedCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesTransportedCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesTransportedCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesTransportedCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesTransportedCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesTransportedCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

local instance reesTransportedCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra (ι := ι) I
local instance reesTransportedCechRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra_scalarTower (ι := ι) I
local instance reesTransportedCechModule :
    Module (MvPolynomial ι (reesAlgebra I)) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)
local instance reesTransportedCechSourceTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_source_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesTransportedCechBaseTower :
    IsScalarTower R (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_base_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesTransportedCechReesTower :
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesTransportedCechBaseGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun n ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G n).restrictScalars R) :=
  reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
local instance reesTransportedCechReesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) :=
  reesProjectivePolynomialGradedSMul (R := R) (M := M) (ι := ι) I G

/-- B[X] 上の Rees 加群の標準開 Čech コホモロジーを B 加群としてまとめる。 -/
def reesAdicProjectiveCechObject (d : ℤ) (q : ℕ) : ModuleCat.{u} (reesAlgebra I) :=
  (fullCechComplex (projectiveNatGradedModuleChartDiagram
    (R := reesAlgebra I) (M := ReesAdicTotalModule (ι := ι) (M := M) I) (ι := ι)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) d)).homology q

/-- Čech コホモロジーの直和へ、Rees 比較によって B 作用を移す。 -/
def reesAdicCechDirectSumTransportedModule (d : ℤ) (q : ℕ) :=
  projectiveScalarRestrictionTransportModuleOfIso
    (reesAdicProjectiveCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

/-- 移した Rees 作用は、直和の既存の R 作用と両立する。 -/
def reesAdicCechDirectSumTransportedScalarTower (d : ℤ) (q : ℕ) :=
  projectiveScalarRestrictionTransportOfIso_scalarTower
    (reesAdicProjectiveCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

/-- 移した作用に関して、直和と Rees の Čech コホモロジーは B 線形に同値。 -/
def reesAdicCechDirectSumTransportedLinearEquiv (d : ℤ) (q : ℕ) :=
  projectiveScalarRestrictionTransportLinearEquivOfIso
    (reesAdicProjectiveCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

/-- B[X] 上の Rees の Čech コホモロジーは B 上有限生成。
原典 Stacks 30.20.1 の Hⁱ の有限性に対応する Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechObject_finite [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    Module.Finite (reesAlgebra I) (reesAdicProjectiveCechObject (R := R) (M := M) (ι := ι) I G d q) := by
  exact reesProjectiveFullCechHomology_finite (R := R) (M := M) (ι := ι) I G d q

/-- 比較で移した作用について、各 IⁿM の Čech コホモロジーの直和は B 上有限生成。
原典 Stacks 30.20.1 の Hⁱ の直和の有限性に対応する Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicCechDirectSumTransportedFinite [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :=
  letI := reesAdicProjectiveCechObject_finite (R := R) (M := M) (ι := ι) I G d q
  projectiveScalarRestrictionTransportOfIso_finite
    (reesAdicProjectiveCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

end SerrePositivity.AlgebraicGeometry
