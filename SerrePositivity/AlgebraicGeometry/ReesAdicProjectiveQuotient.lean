module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveTransition

/-!
概要：I 進閉厚化の実際の商加群に、Proj 次数と多項式環の作用を入れる。
方針：既存の斉次部分加群の商の内部直和を使い、係数環を制限する。
規約：商の型は R 加群としての M/IⁿM とし、多項式作用は同じ商から得る。
使われ方：閉厚化の標準開図式と Čech 長完全列への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R)

/-- I 進閉厚化の実際の商加群 M/IⁿM。 -/
abbrev reesAdicProjectiveQuotient (n : ℕ) :=
  M ⧸ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n

/-- 同じ商加群の、多項式環上の加群構造。 -/
@[instance_reducible]
def reesAdicProjectiveQuotientPolynomialModule (n : ℕ) :
    Module (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (Module (MvPolynomial ι R)
    (M ⧸ ((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
      (⊤ : Submodule (MvPolynomial ι R) M))))

local instance reesQuotientPolynomialModule (n : ℕ) :
    Module (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n

/-- 商における基底作用と多項式作用の両立性。 -/
theorem reesAdicProjectiveQuotientPolynomialModule_scalarTower (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R)
      (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  inferInstanceAs (IsScalarTower R (MvPolynomial ι R)
    (M ⧸ ((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
      (⊤ : Submodule (MvPolynomial ι R) M))))

/-- 閉厚化の商への、多項式環上線形な射影。 -/
def reesAdicProjectiveQuotientProjection (n : ℕ) :
    M →ₗ[MvPolynomial ι R] reesAdicProjectiveQuotient (ι := ι) (M := M) I n :=
  (((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
    (⊤ : Submodule (MvPolynomial ι R) M))).mkQ

/-- 閉厚化の商への射影は全射。 -/
theorem reesAdicProjectiveQuotientProjection_surjective (n : ℕ) :
    Function.Surjective (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).mkQ_surjective

local instance reesQuotientSourcePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n

/-- IⁿM の包含と、閉厚化の商への射影は完全。 -/
theorem reesAdicProjectiveToModule_quotientProjection_exact (n : ℕ) :
    Function.Exact (reesAdicProjectiveToModule (ι := ι) (M := M) I n)
      (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I n) :=
  LinearMap.exact_subtype_mkQ (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)

variable (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

/-- I 進閉厚化の商の Proj 次数成分。 -/
def reesAdicProjectiveQuotientPiece (n d : ℕ) :
    Submodule R (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  SerrePositivity.HilbertSerre.quotientGrade G
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) d

/-- I 進閉厚化の商は、元の Proj 次数の分解を受け継ぐ。 -/
@[instance_reducible]
def reesAdicProjectiveQuotientPieceDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  (SerrePositivity.HilbertSerre.isInternal_quotientGrade G _
    (reesAdicProjectiveSubmodule_isHomogeneous (ι := ι) I G n)).chooseDecomposition

/-- 商への射影は Proj 次数を保つ。 -/
theorem reesAdicProjectiveQuotientProjection_preservesPiece (n d : ℕ)
    (m : M) (hm : m ∈ G d) :
    reesAdicProjectiveQuotientProjection (ι := ι) I n m ∈
      reesAdicProjectiveQuotientPiece (ι := ι) I G n d :=
  ⟨m, hm, rfl⟩

/-- 閉厚化の商の次数と、多項式の次数の作用は両立する。 -/
theorem reesAdicProjectiveQuotientPieceGradedSMul
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G] (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) := by
  refine ⟨?_⟩
  intro i j p x hp hx
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨p • m, SetLike.GradedSMul.smul_mem
    (A := MvPolynomial.homogeneousSubmodule ι R) (B := G) hp hm, rfl⟩

end SerrePositivity.AlgebraicGeometry
