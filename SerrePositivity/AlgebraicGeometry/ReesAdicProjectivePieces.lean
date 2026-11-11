module

public import SerrePositivity.AlgebraicGeometry.ReesExtendedFiltration
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.Subquotient
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
概要：各 IⁿM に、元の加群の Proj 次数を制限する。
方針：既存の次数射影の保存と、斉次な部分加群の次数分解を使う。
規約：I は基底環のイデアル。多項式環へ拡大したイデアルの冪を扱う。
使われ方：Čech 版の Rees 次数の直和比較で、各次数の加群を定める。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- 基底環へ制限した、拡大イデアルの n 乗の作用による部分加群。 -/
def reesAdicProjectiveSubmodule (n : ℕ) : Submodule R M :=
  ((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
    (⊤ : Submodule (MvPolynomial ι R) M)).restrictScalars R

/-- IⁿM は、元の Proj 次数について斉次。 -/
theorem reesAdicProjectiveSubmodule_isHomogeneous (n : ℕ) :
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).IsHomogeneous G := by
  intro d x hx
  exact reesExtendedAdic_decompose_mem (S := MvPolynomial ι R) I G d n x hx

/-- IⁿM 内の Proj 次数成分。 -/
def reesAdicProjectivePiece (n d : ℕ) :
    Submodule R (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  SerrePositivity.HilbertSerre.submoduleGrade G
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) d

/-- IⁿM の Proj 次数分解。 -/
@[instance_reducible]
def reesAdicProjectivePieceDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectivePiece (ι := ι) I G n) :=
  (SerrePositivity.HilbertSerre.isInternal_submoduleGrade G _
    (reesAdicProjectiveSubmodule_isHomogeneous (ι := ι) I G n)).chooseDecomposition

/-- IⁿM の多項式環上の加群構造。 -/
@[instance_reducible]
def reesAdicProjectivePolynomialModule (n : ℕ) :
    Module (MvPolynomial ι R) (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  inferInstanceAs (Module (MvPolynomial ι R)
    ↥((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
      (⊤ : Submodule (MvPolynomial ι R) M)))

/-- 制限した基底作用と、多項式作用の両立性。 -/
theorem reesAdicProjectivePolynomialModule_scalarTower (n : ℕ) :
    letI := reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
    IsScalarTower R (MvPolynomial ι R)
      (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) := by
  letI := reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
  exact inferInstanceAs (IsScalarTower R (MvPolynomial ι R)
    ↥((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
      (⊤ : Submodule (MvPolynomial ι R) M)))

/-- 制限した Proj 次数は、元の多項式の標準次数の作用と両立する。 -/
theorem reesAdicProjectivePieceGradedSMul
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G] (n : ℕ) :
    letI := reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) := by
  letI := reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
  refine ⟨?_⟩
  intro i j a x ha hx
  change a • x.val ∈ G (i + j)
  have hx' : x.val ∈ G j := hx
  exact SetLike.GradedSMul.smul_mem (A := MvPolynomial.homogeneousSubmodule ι R) (B := G) ha hx'

/-- 有限な多項式加群の各 IⁿM は、多項式環上有限生成。 -/
theorem reesAdicProjectivePolynomialModule_finite [IsNoetherianRing R] [Finite ι]
    [Module.Finite (MvPolynomial ι R) M] (n : ℕ) :
    letI := reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
    Module.Finite (MvPolynomial ι R)
      (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) := by
  letI := reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
  exact inferInstanceAs (Module.Finite (MvPolynomial ι R)
    ↥((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
      (⊤ : Submodule (MvPolynomial ι R) M)))

end SerrePositivity.AlgebraicGeometry
