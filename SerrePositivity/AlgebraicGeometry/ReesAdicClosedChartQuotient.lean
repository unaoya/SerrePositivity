module

public import SerrePositivity.AlgebraicGeometry.ReesAdicChartIdealRange
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartExact

/-!
概要：Rees の閉厚化の標準開の商を、元の標準開の Iⁿ 倍による商と照合する。
方針：次数ごとの完全性と、包含の像の Iⁿ 倍への一致を使う。
規約：非 flat な H とテンソル積の交換は使わない。
使われ方：実際の閉厚化のアフィン切断の商表示と同じ核で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance closedChartKernelSourceModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance closedChartKernelSourceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance closedChartKernelSourceGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance closedChartKernelSourceDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceDecomposition (ι := ι) I G n
local instance closedChartKernelQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance closedChartKernelQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance closedChartKernelQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n
local instance closedChartKernelQuotientDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) I G n

/-- Rees の閉厚化の列は、各標準開の指定次数部分でも完全。 -/
theorem reesAdicProjectiveClosedChart_exact (n : ℕ) (d : ℤ) (T : Finset ι) :
    Function.Exact (((reesAdicProjectiveCechInclusionChartMap (ι := ι) I G n d).app T).hom)
      (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d).app T).hom) :=
  projectiveNatChartMap_exact (reesAdicProjectivePiece (ι := ι) I G n) G
    (reesAdicProjectiveQuotientPiece (ι := ι) I G n)
    (reesAdicProjectiveToModule (ι := ι) (M := M) I n)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I n)
    (reesAdicProjectiveToModule_preservesPiece (ι := ι) I G n)
    (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) I G n)
    (reesAdicProjectiveToModule_quotientProjection_exact (ι := ι) (M := M) I n) d T

/-- 閉厚化への射影は、各標準開の指定次数部分へ全射。 -/
theorem reesAdicProjectiveClosedChartProjection_surjective (n : ℕ) (d : ℤ) (T : Finset ι) :
    Function.Surjective (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d).app T).hom) :=
  projectiveNatChartMap_surjective G (reesAdicProjectiveQuotientPiece (ι := ι) I G n)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I n)
    (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) I G n)
    (reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I n) d T

/-- 閉厚化への指定次数の標準開の射の核は、元の成分の Iⁿ 倍。 -/
theorem reesAdicProjectiveClosedChartProjection_ker (n : ℕ) (d : ℤ) (T : Finset ι) :
    LinearMap.ker (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d).app T).hom) =
      I ^ n • (⊤ : Submodule R ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T)) := by
  ext y
  rw [← reesAdicProjectiveChartInclusion_range_ideal (ι := ι) I G n d T]
  exact reesAdicProjectiveClosedChart_exact (ι := ι) I G n d T y

/-- Rees の閉厚化の標準開は、元の標準開の指定次数成分の Iⁿ 倍による商。 -/
def reesAdicProjectiveClosedChartQuotientIso (n : ℕ) (d : ℤ) (T : Finset ι) :
    (((projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) ⧸
      I ^ n • (⊤ : Submodule R ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T))) ≃ₗ[R]
      ((projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectiveQuotientPiece (ι := ι) I G n) d).obj T) :=
  (Submodule.quotEquivOfEq _ _ (reesAdicProjectiveClosedChartProjection_ker (ι := ι) I G n d T).symm).trans
    ((((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d).app T).hom).quotKerEquivOfSurjective
      (reesAdicProjectiveClosedChartProjection_surjective (ι := ι) I G n d T))

/-- 商の同型は、元の標準開の成分を元の Rees の射影で送る。 -/
theorem reesAdicProjectiveClosedChartQuotientIso_mk (n : ℕ) (d : ℤ) (T : Finset ι)
    (x : (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) :
    reesAdicProjectiveClosedChartQuotientIso (ι := ι) I G n d T (Submodule.Quotient.mk x) =
      (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d).app T).hom x) := rfl

end SerrePositivity.AlgebraicGeometry
