module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotient
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatCechExact

/-!
概要：実際の閉厚化 M/IⁿM の標準開図式と、Čech 複体の短完全列を作る。
方針：IⁿM とその商の次数分解を使い、次数付き短完全列を標準開へ移す。
規約：閉厚化の対象は実際の商加群であり、形式的な余核を入力とはしない。
使われ方：閉厚化の Čech 長完全列と Rees の評価を結ぶ。
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

local instance closedCechSourceModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance closedCechSourceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance closedCechSourceGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance closedCechSourceDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceDecomposition (ι := ι) I G n
local instance closedCechQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance closedCechQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance closedCechQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n
local instance closedCechQuotientDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) I G n

/-- IⁿM の包含から得られる、標準開の係数図式の写像。 -/
def reesAdicProjectiveCechInclusionChartMap (n : ℕ) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (ι := ι) (reesAdicProjectivePiece (ι := ι) I G n) G
    (reesAdicProjectiveToModule (ι := ι) (M := M) I n)
      (reesAdicProjectiveToModule_preservesPiece (ι := ι) I G n) d

/-- 実際の閉厚化の商への射影が誘導する、標準開の係数図式の写像。 -/
def reesAdicProjectiveClosedCechProjectionChartMap (n : ℕ) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (ι := ι) G (reesAdicProjectiveQuotientPiece (ι := ι) I G n)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I n)
      (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) I G n) d

/-- 実際の I 進閉厚化の列は、標準開の全タプル Čech 複体でも短完全。 -/
theorem reesAdicProjectiveClosedCech_shortExact (n : ℕ) (d : ℤ) :
    ∃ hzero : reesAdicProjectiveCechInclusionChartMap (ι := ι) I G n d ≫
        reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d = 0,
      ((ShortComplex.mk (reesAdicProjectiveCechInclusionChartMap (ι := ι) I G n d)
        (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d) hzero).map
          (fullCechComplexFunctor (R := R) (ι := ι))).ShortExact := by
  apply projectiveNatFullCech_shortExact (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G n) G
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) d
    (reesAdicProjectiveToModule (ι := ι) (M := M) I n)
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I n)
    (reesAdicProjectiveToModule_preservesPiece (ι := ι) I G n)
    (reesAdicProjectiveQuotientProjection_preservesPiece (ι := ι) I G n)
  · intro x y h
    exact Subtype.ext h
  · exact reesAdicProjectiveToModule_quotientProjection_exact (ι := ι) (M := M) I n
  · exact reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I n

/-- 実際の I 進閉厚化の全タプル Čech 複体からなる短複体。 -/
def reesAdicProjectiveClosedCechShortComplex (n : ℕ) (d : ℤ) :=
  (ShortComplex.mk (reesAdicProjectiveCechInclusionChartMap (ι := ι) I G n d)
    (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d)
    (reesAdicProjectiveClosedCech_shortExact (ι := ι) I G n d).choose).map
      (fullCechComplexFunctor (R := R) (ι := ι))

/-- 実際の閉厚化から作った Čech の短複体は短完全。 -/
theorem reesAdicProjectiveClosedCechShortComplex_shortExact (n : ℕ) (d : ℤ) :
    (reesAdicProjectiveClosedCechShortComplex (ι := ι) I G n d).ShortExact :=
  (reesAdicProjectiveClosedCech_shortExact (ι := ι) I G n d).choose_spec

end SerrePositivity.AlgebraicGeometry
