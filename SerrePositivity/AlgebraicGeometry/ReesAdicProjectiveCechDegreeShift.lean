module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveDegreeShift
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap

/-!
概要：Rees の各次数間の作用を、Proj 標準開と Čech コホモロジーの写像にする。
方針：Iⁱ の元による写像が Proj 次数を保つことを、自然数次数の API に渡す。
規約：Rees 次数は j から i+j へ移し、捻り d と Čech 次数 q は固定する。
使われ方：Stacks 30.20.1 の直和に作用する、実際の斉次 Rees 係数の写像。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesDegreeShiftCechPolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesDegreeShiftCechTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesDegreeShiftCechGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n

/-- a∈Iⁱ の作用が誘導する、Rees 次数 j と i+j の標準開係数図式間の写像。 -/
def reesAdicProjectiveDegreeShiftChartMap
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (R := R) (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G j)
    (reesAdicProjectivePiece (ι := ι) I G (i + j))
    (reesAdicProjectiveDegreeShift (ι := ι) (M := M) I i j a ha)
    (fun n m hm ↦ reesAdicProjectiveDegreeShift_preservesPiece I G i j n a ha m hm) d

/-- a∈Iⁱ の作用が誘導する、Rees 次数 j と i+j の Čech コホモロジー間の写像。
原典 Stacks 30.20.1 の Hⁱ の直和に対する斉次作用に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveDegreeShiftCechHomologyMap
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ) :=
  projectiveNatGradedModuleCechHomologyMap (R := R) (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G j)
    (reesAdicProjectivePiece (ι := ι) I G (i + j))
    (reesAdicProjectiveDegreeShift (ι := ι) (M := M) I i j a ha)
    (fun n m hm ↦ reesAdicProjectiveDegreeShift_preservesPiece I G i j n a ha m hm) d q

end SerrePositivity.AlgebraicGeometry
