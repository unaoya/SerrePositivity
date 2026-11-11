module

public import SerrePositivity.AlgebraicGeometry.ReesCoefficientAdicCechTransition
public import SerrePositivity.AlgebraicGeometry.ReesClosedCoefficientNaturality
public import SerrePositivity.AlgebraicGeometry.ReesClosedThickeningNaturality

/-!
概要：M/JM の商係数表示を、実際の I 進遷移・互換族・形式関数へ接続する。
方針：R/J を固定した係数比較を特殊化し、証明済みの形式関数と合成する。
規約：R 上のコホモロジーの完備化を、R/J 上で計算した各閉厚化の互換族と比較する。
使われ方：§9 の閉厚化との整合性を、元の M からの射影と可換な形で供給する。
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

variable (I : Ideal R) [LinearOrder ι] [Fintype ι]

local instance : Fact (Function.Surjective (algebraMap R (R ⧸ J))) :=
  ⟨Ideal.Quotient.mk_surjective⟩
local instance : DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1
local instance : DirectSum.Decomposition
    (fun a ↦ (reesClosedCoefficientPiece (ι := ι) J G a).restrictScalars R) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1

/-- M/JM の実際の I 進閉厚化の、商係数 Čech 計算との比較。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedCoefficientAdicCechIso (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n d q ≅
      reesCoefficientAdicRestrictedCechHomology (R := R) (B := R ⧸ J) (ι := ι) I
        (reesClosedCoefficientPiece (ι := ι) J G) n d q := by
  exact reesCoefficientAdicCechIso (R := R) (B := R ⧸ J) (ι := ι) I
    (reesClosedCoefficientPiece (ι := ι) J G) n d q

/-- 閉厚化の商係数比較は、以前の実際の I 進 Čech 遷移と可換。
原典 Stacks 30.20.5 の Hⁱ に対応する Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCoefficientAdicCechIso_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechTransition (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) i j h d q ≫
      (reesClosedCoefficientAdicCechIso J G I j d q).hom =
    (reesClosedCoefficientAdicCechIso J G I i d q).hom ≫
      reesCoefficientAdicRestrictedCechTransition (R := R) (B := R ⧸ J) (ι := ι) I
        (reesClosedCoefficientPiece (ι := ι) J G) i j h d q := by
  convert reesCoefficientAdicCechIso_transition (R := R) (B := R ⧸ J) (ι := ι) I
    (reesClosedCoefficientPiece (ι := ι) J G) i j h d q using 1 <;> rfl

/-- 閉厚化の実際の互換族を、R/J 上の Čech 計算の互換族へ送る同型。 -/
def reesClosedCoefficientAdicCechFamiliesEquiv (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q ≃ₗ[R]
      reesCoefficientAdicRestrictedCechFamilies (R := R) (B := R ⧸ J) (ι := ι) I
        (reesClosedCoefficientPiece (ι := ι) J G) d q :=
  compatibleLinearFamiliesEquiv _ _
    (fun n ↦ (reesClosedCoefficientAdicCechIso J G I n d q).toLinearEquiv)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (reesClosedCoefficientAdicCechIso_transition J G I i j h d q).symm)

/-- 元の M の閉厚化の互換族から、商係数で表示した M/JM の互換族への写像。 -/
def reesClosedCoefficientAdicCechFamiliesMap (d : ℤ) (q : ℕ) :=
  (reesClosedCoefficientAdicCechFamiliesEquiv J G I d q).toLinearMap.comp
    (reesClosedThickeningCechFamiliesMap (ι := ι) I J G d q)

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) M]
local instance : Module.Finite (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  inferInstanceAs (Module.Finite (MvPolynomial ι R)
    (M ⧸ ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
      (⊤ : Submodule (MvPolynomial ι R) M))))

/-- M/JM の Čech 形式関数を、R/J 上の各閉厚化の計算を用いて表す同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedCoefficientAdicCechFormalFunctions (d : ℤ) (q : ℕ) :
    AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι)
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q) ≃ₗ[R]
      reesCoefficientAdicRestrictedCechFamilies (R := R) (B := R ⧸ J) (ι := ι) I
        (reesClosedCoefficientPiece (ι := ι) J G) d q :=
  (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q).trans
      (reesClosedCoefficientAdicCechFamiliesEquiv J G I d q)

/-- 商係数で表した Čech 形式関数も、元の M からの閉厚化射影と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に対応する Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedCoefficientAdicCechFormalFunctions_naturality (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesClosedCoefficientAdicCechFormalFunctions J G I d q
        (AdicCompletion.map I (reesClosedThickeningCechHomologyMap (ι := ι) J G d q).hom a) =
      reesClosedCoefficientAdicCechFamiliesMap J G I d q
        (reesAdicProjectiveClosedCechCompletionMap (ι := ι) I G d q a) := by
  exact congrArg (reesClosedCoefficientAdicCechFamiliesEquiv J G I d q)
    (reesClosedThickeningCechCompletionLinearEquiv_naturality (ι := ι) I J G d q a).symm

end SerrePositivity.AlgebraicGeometry
