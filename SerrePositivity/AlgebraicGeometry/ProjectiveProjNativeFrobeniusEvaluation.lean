module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechEvaluation
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobenius
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechFrobenius

/-!
概要：次数零局所化で計算した Frobenius を、実際の構造層の p 乗と照合する。
方針：一つの斉次分数に戻し、分子と分母の両方を p 乗する。
規約：零環となる標準開を含み、局所化の非自明性を仮定しない。
使われ方：共通細分と I 進遷移の実際の Frobenius への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (p : ℕ) (hp : p.Prime) [ExpChar R p] (hz : (p : S) = 0)
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 捻り零の Frobenius は、同じ次数零チャートへの半線形写像。 -/
def projectiveNatGradedChartZeroFrobenius (T : Finset ι) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T →ₛₗ[frobenius R p]
      (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T := by
  convert projectiveNatGradedChartFrobenius p hp hz G T 0 using 1 <;> first | rfl | simp only [mul_zero]

/-- 捻り零の Frobenius の周囲の局所化への像。 -/
theorem projectiveNatGradedChartZeroFrobenius_val (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    (projectiveNatGradedChartZeroFrobenius p hp hz G T z).val =
      projectiveLocalizedFrobenius p hp (Submonoid.powers (projectiveLaurentDenominator R T))
        hz z.val := by
  dsimp only [projectiveNatGradedChartZeroFrobenius]
  rfl

/-- 加群のチャートの Frobenius は、実際の斉次局所化の p 乗に一致する。 -/
theorem projectiveHomogeneousChartLinearEquiv_frobenius (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    projectiveHomogeneousChartLinearEquiv G T (projectiveNatGradedChartZeroFrobenius p hp hz G T z) =
      (projectiveHomogeneousChartLinearEquiv G T z) ^ p := by
  obtain ⟨n, m, hm, hfrac⟩ := HomogeneousLocalization.Away.mk_surjective G
    (projectivePolynomialDenominatorImage_mem G T) (projectiveHomogeneousChartLinearEquiv G T z)
  have hz' := projectiveHomogeneousChartLinearEquiv_fraction_reflect G T n m hm z hfrac.symm
  have hm' : m ^ p ∈ G ((p * n) • T.card) := by
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_assoc] using SetLike.pow_mem_graded (A := G) p hm
  have hF : (projectiveNatGradedChartZeroFrobenius p hp hz G T z).val =
      LocalizedModule.mk (m ^ p) (projDenominator (projectiveLaurentDenominator R T) (p * n)) := by
    rw [projectiveNatGradedChartZeroFrobenius_val, hz', projectiveLocalizedFrobenius_fraction]
  rw [projectiveHomogeneousChartLinearEquiv_fraction G T (p * n) (m ^ p) hm' _ hF, ← hfrac]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow]
  congr 1
  apply Subtype.ext <;> simp only [projDenominator, SubmonoidClass.coe_pow,
    ← pow_mul, Nat.mul_comm]

/-- 分数の比較を実際の標準開の切断へ移しても Frobenius は p 乗に一致する。 -/
theorem projectiveProjNativeChart_frobenius (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    (Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
      (projectiveLaurentDenominator R T))).hom
      (projectiveHomogeneousChartLinearEquiv G T
        (projectiveNatGradedChartZeroFrobenius p hp hz G T z)) =
    ((Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
      (projectiveLaurentDenominator R T))).hom (projectiveHomogeneousChartLinearEquiv G T z)) ^ p := by
  rw [projectiveHomogeneousChartLinearEquiv_frobenius, map_pow]

end SerrePositivity.AlgebraicGeometry
