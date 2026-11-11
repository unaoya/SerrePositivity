module

public import SerrePositivity.AlgebraicGeometry.ReesIteratedClosedCechTransition
public import SerrePositivity.AlgebraicGeometry.ReesClosedThickeningNaturality
public import SerrePositivity.AlgebraicGeometry.LinearCompatibleFamiliesEquiv

/-!
概要：M/JM の Čech 形式関数を、M/(JM+IⁿM) の互換族で表す。
方針：遷移と可換な各段の Čech 同型を互換族へまとめ、完備化同型と合成する。
規約：非 flat な閉厚化も含め、基底環上線形に述べる。
使われ方：§9 の閉厚化の整合性を、実際の一重の商で使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I J : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance thickeningFamiliesModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) J 1
local instance thickeningFamiliesTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) J 1
local instance thickeningFamiliesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
local instance thickeningFamiliesDecomposition :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1
local instance thickeningFamiliesQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance thickeningFamiliesQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n
local instance thickeningFamiliesQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n

local instance thickeningFamiliesSumGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesIteratedClosedSumPiece (ι := ι) I J G n) :=
  reesIteratedClosedSumPieceGradedSMul (ι := ι) I J G n

/-- 一重の商 M/(JM+IⁿM) の Čech コホモロジーの互換族。 -/
def reesIteratedClosedSumCechFamilies (d : ℤ) (q : ℕ) :
    Submodule R (∀ n, reesIteratedClosedSumCechHomology (ι := ι) I J G n d q) :=
  compatibleLinearFamilies
    (fun i j h ↦ (reesIteratedClosedSumCechTransition (ι := ι) I J G i j h d q).hom)

/-- 二重閉厚化と一重の商の Čech 比較を、互換族の線形同型へまとめる。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる、閉厚化の比較の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesIteratedClosedCechFamiliesEquiv (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q ≃ₗ[R]
      reesIteratedClosedSumCechFamilies (ι := ι) I J G d q :=
  compatibleLinearFamiliesEquiv
    (fun i j h ↦ (reesAdicProjectiveClosedCechTransition (ι := ι) I
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) i j h d q).hom)
    (fun i j h ↦ (reesIteratedClosedSumCechTransition (ι := ι) I J G i j h d q).hom)
    (fun n ↦ (reesIteratedClosedCechHomologyIso (ι := ι) I J G n d q).toLinearEquiv)
    (fun i j h ↦ congrArg ModuleCat.Hom.hom
      (reesIteratedClosedCechHomologyIso_transition (ι := ι) I J G i j h d q))

/-- 元の M の閉厚化の互換族を、一重の商の Čech 互換族へ送る。 -/
def reesClosedThickeningSumCechFamiliesMap (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q →ₗ[R]
      reesIteratedClosedSumCechFamilies (ι := ι) I J G d q :=
  (reesIteratedClosedCechFamiliesEquiv (ι := ι) I J G d q).toLinearMap.comp
    (reesClosedThickeningCechFamiliesMap (ι := ι) I J G d q)

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) M]
local instance thickeningFamiliesFinite : Module.Finite (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  inferInstanceAs (Module.Finite (MvPolynomial ι R)
    (M ⧸ ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
      (⊤ : Submodule (MvPolynomial ι R) M))))

/-- M/JM の Čech コホモロジーの完備化を、M/(JM+IⁿM) の互換族と比較する同型。
原典 Stacks 30.20.5 の Hⁱ の形式関数の、閉厚化に対する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedThickeningSumCechFormalFunctions (d : ℤ) (q : ℕ) :
    AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι)
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q) ≃ₗ[R]
      reesIteratedClosedSumCechFamilies (ι := ι) I J G d q :=
  (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q).trans
    (reesIteratedClosedCechFamiliesEquiv (ι := ι) I J G d q)

/-- 一重の商で表した閉厚化の Čech 形式関数も、元の M からの射影と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数の、閉厚化の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedThickeningSumCechFormalFunctions_naturality (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesClosedThickeningSumCechFamiliesMap (ι := ι) I J G d q
        (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G d q a) =
      reesClosedThickeningSumCechFormalFunctions (ι := ι) I J G d q
        (AdicCompletion.map I (reesClosedThickeningCechHomologyMap (ι := ι) J G d q).hom a) :=
  congrArg (reesIteratedClosedCechFamiliesEquiv (ι := ι) I J G d q)
    (reesClosedThickeningCechCompletionLinearEquiv_naturality (ι := ι) I J G d q a)

end SerrePositivity.AlgebraicGeometry
