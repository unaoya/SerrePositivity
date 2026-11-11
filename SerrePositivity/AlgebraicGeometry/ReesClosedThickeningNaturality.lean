module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechModuleNaturality

/-!
概要：M→M/JM による、実際の閉厚化と Čech 形式関数の整合性。
方針：商の次数分解を使い、証明済みの加群写像の自然性を射影へ適用する。
規約：flat 性を仮定せず、すべてを基底環上の写像として扱う。
使われ方：§9 の閉厚化との整合性に使う、実際の商加群での可換図式。
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

local instance thickeningModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) J 1
local instance thickeningTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) J 1
local instance thickeningGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
local instance thickeningDecomposition :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1

/-- M→M/JM が誘導する、元の標準開 Čech コホモロジーの写像。 -/
def reesClosedThickeningCechHomologyMap (d : ℤ) (q : ℕ) :=
  projectiveNatGradedModuleCechHomologyMap G (reesAdicProjectiveQuotientPiece (ι := ι) J G 1)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) J 1)
    (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) J G 1) d q

/-- M→M/JM が誘導する、I 進閉厚化の Čech 互換族の間の写像。 -/
def reesClosedThickeningCechFamiliesMap (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I G d q →ₗ[R]
      reesAdicProjectiveClosedCechCompatibleFamilies (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q :=
  reesAdicProjectiveClosedCechModuleFamiliesMap I G
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) J 1)
    (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) J G 1) d q

/-- 実際の M/JM への閉厚化は、完備化からの標準 Čech 写像と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる、閉厚化の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedThickeningCechCompletionMap_naturality (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesClosedThickeningCechFamiliesMap I J G d q
        (reesAdicProjectiveClosedCechCompletionMap (ι := ι) I G d q a) =
      reesAdicProjectiveClosedCechCompletionMap (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q
        (AdicCompletion.map I (reesClosedThickeningCechHomologyMap J G d q).hom a) :=
  reesAdicProjectiveClosedCechCompletionMap_module_naturality I G
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) J 1)
    (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) J G 1) d q a

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) M]
local instance thickeningFinite : Module.Finite (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  inferInstanceAs (Module.Finite (MvPolynomial ι R)
    (M ⧸ ((J.map (algebraMap R (MvPolynomial ι R))) ^ 1 •
      (⊤ : Submodule (MvPolynomial ι R) M))))

/-- Čech 形式関数の同型は、実際の M/JM への閉厚化と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる、閉厚化の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedThickeningCechCompletionLinearEquiv_naturality (d : ℤ) (q : ℕ)
    (a : AdicCompletion I (reesAdicProjectiveCechTarget (ι := ι) G d q)) :
    reesClosedThickeningCechFamiliesMap I J G d q
        (reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I G d q a) =
      reesAdicProjectiveClosedCechCompletionLinearEquiv (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) d q
        (AdicCompletion.map I (reesClosedThickeningCechHomologyMap J G d q).hom a) :=
  reesAdicProjectiveClosedCechCompletionLinearEquiv_module_naturality I G
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) J 1)
    (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) J G 1) d q a

end SerrePositivity.AlgebraicGeometry
