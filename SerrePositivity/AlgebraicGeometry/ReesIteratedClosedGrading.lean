module

public import SerrePositivity.AlgebraicGeometry.ReesIteratedClosedQuotient
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedEquiv
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechHomology

/-!
概要：二重閉厚化と一つの商の比較は、Proj 次数と Čech 計算も保つ。
方針：両方の次数成分を、元の次数成分からの像で表す。
規約：分母の和を多項式加群として扱い、flat 性は仮定しない。
使われ方：§9 の非 flat な閉厚化の、実際の係数と Čech コホモロジーの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I J : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance iteratedGradeModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) J 1
local instance iteratedGradeTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) J 1
local instance iteratedGradeGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
local instance iteratedGradeDecomposition :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1
local instance iteratedGradeQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance iteratedGradeQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n
local instance iteratedGradeQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n

/-- 単一の商 M/(JM+IⁿM) における、元の Proj 次数成分の像。 -/
def reesIteratedClosedSumPiece (n d : ℕ) :
    Submodule R (M ⧸ (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
      reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n)) :=
  (G d).map ((reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
    reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n).mkQ.restrictScalars R)

/-- 二重閉厚化から単一の商への同型は、元の Proj 次数を保つ。 -/
theorem reesIteratedClosedQuotientLinearEquiv_preservesPiece (n d : ℕ)
    (x : reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n)
    (hx : x ∈ reesAdicProjectiveQuotientPiece (ι := ι) I
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n d) :
    reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J n x ∈
      reesIteratedClosedSumPiece (ι := ι) I J G n d := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  exact ⟨m, hm, rfl⟩

/-- 単一の商から二重閉厚化への逆写像も、元の Proj 次数を保つ。 -/
theorem reesIteratedClosedQuotientLinearEquiv_symm_preservesPiece (n d : ℕ)
    (y : M ⧸ (reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
      reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n))
    (hy : y ∈ reesIteratedClosedSumPiece (ι := ι) I J G n d) :
    (reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J n).symm y ∈
      reesAdicProjectiveQuotientPiece (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n d := by
  obtain ⟨m, hm, rfl⟩ := hy
  change (reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J n).symm
      (reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J n
        (Submodule.Quotient.mk (Submodule.Quotient.mk m))) ∈ _
  rw [LinearEquiv.symm_apply_apply]
  exact ⟨Submodule.Quotient.mk m, ⟨m, hm, rfl⟩, rfl⟩

/-- 単一の商の Proj 次数と、多項式の次数の作用は両立する。 -/
theorem reesIteratedClosedSumPieceGradedSMul (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesIteratedClosedSumPiece (ι := ι) I J G n) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R) (B := G) hp hm, rfl⟩

local instance iteratedSumGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesIteratedClosedSumPiece (ι := ι) I J G n) := reesIteratedClosedSumPieceGradedSMul (ι := ι) I J G n

variable [LinearOrder ι] [Fintype ι]

/-- 二重閉厚化と M/(JM+IⁿM) の標準開 Čech コホモロジーの比較同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる、閉厚化の比較の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesIteratedClosedCechHomologyIso (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n d q ≅
      (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesIteratedClosedSumPiece (ι := ι) I J G n) d)).homology q :=
  projectiveNatGradedModuleCechHomologyIso
    (reesAdicProjectiveQuotientPiece (ι := ι) I
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n)
    (reesIteratedClosedSumPiece (ι := ι) I J G n)
    (reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J n)
    (reesIteratedClosedQuotientLinearEquiv_preservesPiece (ι := ι) I J G n)
    (reesIteratedClosedQuotientLinearEquiv_symm_preservesPiece (ι := ι) I J G n) d q

end SerrePositivity.AlgebraicGeometry
