module

public import SerrePositivity.AlgebraicGeometry.ReesAdicDirectSumGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizedDirectSum
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationCongr

/-!
概要：Rees 加群の指定 Proj 次数の局所化を、各 IⁿM の斉次局所化の直和と比較する。
方針：分子の次数を保つ Rees 同値を局所化し、斉次局所化と直和を交換する。
規約：分母の第 k 冪で許される Proj 次数は任意の族 ν k として指定する。
使われ方：Proj 標準開の Rees–Čech 比較。次数零では ν k を分母の次数の k 倍に取る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

local instance reesGradedLocalizedPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesGradedLocalizedPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesGradedLocalizedPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesGradedLocalizedPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesGradedLocalizedPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesGradedLocalizedTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesGradedLocalizedTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesGradedLocalizedPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesGradedLocalizedTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesGradedLocalizedTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesGradedLocalizedTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

/-- Rees 同値の分子の次数は、各 IⁿM の同じ Proj 次数に対応する。 -/
theorem reesAdicDirectSumPolynomialLinearEquiv_projective_mem (d : ℕ)
    (x : ⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :
    reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I x ∈
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G d).restrictScalars R ↔
      x ∈ projectiveDirectSumSubmodule (fun n ↦ reesAdicProjectivePiece (R := R) (M := M) (ι := ι) I G n d) := by
  change reesAdicDirectSumLinearEquiv (ι := ι) (M := M) I x ∈
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G d).restrictScalars R ↔ _
  rw [reesAdicDirectSumLinearEquiv_mem_iff (M := M) (ι := ι), mem_projectiveDirectSumSubmodule]
  rfl

/-- 指定 Proj 次数の Rees 局所化と、各 IⁿM の同じ次数の局所化の直和の同値。 -/
def reesAdicGradedLocalizedDirectSumLinearEquiv (f : MvPolynomial ι R) (ν : ℕ → ℕ)
    (hf : ∀ k m, m ∈ G (ν k) → f • m ∈ G (ν (k + 1))) :=
  @projectiveGradedLocalizedDirectSumTransport R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I)
    inferInstance inferInstance inferInstance inferInstance
    (reesAdicTotalBaseModule (ι := ι) (M := M) I) inferInstance
    (IsScalarTower.of_compHom R (MvPolynomial ι R) _)
    ℕ inferInstance (fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (fun n ↦ inferInstance) (fun n ↦ inferInstance)
    (fun n ↦ reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n)
    (fun n ↦ reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n)
    f (fun n k ↦ reesAdicProjectivePiece (R := R) (M := M) (ι := ι) I G n (ν k))
    (fun k ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G (ν k)).restrictScalars R)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (fun k x ↦ reesAdicDirectSumPolynomialLinearEquiv_projective_mem
      (M := M) (ι := ι) I G (ν k) x)
    (fun n k m ↦ hf k m.val.val m.property)

end SerrePositivity.AlgebraicGeometry
