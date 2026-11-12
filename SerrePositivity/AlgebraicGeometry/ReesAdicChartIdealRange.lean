module

public import SerrePositivity.AlgebraicGeometry.ReesAdicIdealPiece
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedAwayIdealRange
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveClosedCech

/-!
概要：IⁿM の包含が標準開の指定成分に誘導する写像の像を、Iⁿ 倍として同定する。
方針：分子ごとのイデアル倍の像の等式を斉次局所化へ移す。
規約：商への flat 底変換は使わない。
使われ方：Rees の商の Čech 係数と、実際の閉厚化の切断の核を照合する。
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
local instance idealChartSourceModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance idealChartSourceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance idealChartSourceGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n

/-- IⁿM から元の標準開の次数 d 成分への写像の像は、同じ成分の Iⁿ 倍。 -/
theorem reesAdicProjectiveChartInclusion_range_ideal (n : ℕ) (d : ℤ) (T : Finset ι) :
    LinearMap.range (((reesAdicProjectiveCechInclusionChartMap (ι := ι) I G n d).app T).hom) =
      I ^ n • (⊤ : Submodule R ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T)) := by
  letI := projectiveNatGradingIntSMul (ι := ι) G
  let V := fun k : ℕ ↦ projectiveNatGradingInt
    (reesAdicProjectivePiece (ι := ι) I G n) (d + k • (T.card : ℤ))
  let W := fun k : ℕ ↦ projectiveNatGradingInt G (d + k • (T.card : ℤ))
  let f := reesAdicProjectiveToModule (ι := ι) (M := M) I n
  have hf : ∀ k, ∀ m ∈ V k, f m ∈ W k := fun k ↦
    projectiveNatGradingInt_map_mem (reesAdicProjectivePiece (ι := ι) I G n) G f
      (reesAdicProjectiveToModule_preservesPiece (ι := ι) I G n) (d + k • (T.card : ℤ))
  change LinearMap.range (projectiveGradedAwayMap (projectiveLaurentDenominator R T)
    V W f hf) = I ^ n • (⊤ : Submodule R (projectiveGradedAway (projectiveLaurentDenominator R T) W))
  apply projectiveGradedAwayMap_range_ideal
  · intro k
    exact reesAdicProjectiveIntPiece_image_eq_ideal_smul (ι := ι) I G n _
  · exact projectiveGradedChart_mul_denominator (projectiveNatGradingInt G) T d

end SerrePositivity.AlgebraicGeometry
