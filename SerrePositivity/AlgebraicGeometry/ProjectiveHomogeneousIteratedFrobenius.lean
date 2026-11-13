module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechEvaluation
public import SerrePositivity.AlgebraicGeometry.ProjectiveChartIteratedFrobenius

/-!
概要：次数零チャートの反復 Frobenius を、標準開の環の実際の冪と照合する。
方針：斉次分数の分子と分母の p^e 乗を比較する。
規約：元の環・商・標準開の零環を排除しない。
使われ方：加群の Frobenius 係数系と標準開環の Frobenius 順極限を同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 加群のチャートの反復 Frobenius は、斉次局所化の実際の p^e 乗と一致する。 -/
theorem projectiveHomogeneousChartLinearEquiv_iteratedFrobenius (T : Finset ι) (e : ℕ)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    projectiveHomogeneousChartLinearEquiv G T
        (projectiveChartIteratedFrobenius G p hp hR hA T e z) =
      (projectiveHomogeneousChartLinearEquiv G T z) ^ (p ^ e) := by
  obtain ⟨n, m, hm, hfrac⟩ := HomogeneousLocalization.Away.mk_surjective G
    (projectivePolynomialDenominatorImage_mem G T) (projectiveHomogeneousChartLinearEquiv G T z)
  have hz' := projectiveHomogeneousChartLinearEquiv_fraction_reflect G T n m hm z hfrac.symm
  have hm' : m ^ (p ^ e) ∈ G ((p ^ e * n) • T.card) := by
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_assoc] using
      SetLike.pow_mem_graded (A := G) (p ^ e) hm
  have hF : (projectiveChartIteratedFrobenius G p hp hR hA T e z).val =
      LocalizedModule.mk (m ^ (p ^ e))
        (projDenominator (projectiveLaurentDenominator R T) (p ^ e * n)) := by
    rw [projectiveChartIteratedFrobenius_val, hz', LocalizedModule.mk_pow]
    congr 1
    apply Subtype.ext
    change (projectiveLaurentDenominator R T ^ n) ^ (p ^ e) =
      projectiveLaurentDenominator R T ^ (p ^ e * n)
    simp only [pow_mul, Nat.mul_comm]
  rw [projectiveHomogeneousChartLinearEquiv_fraction G T (p ^ e * n)
    (m ^ (p ^ e)) hm' _ hF, ← hfrac]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow]
  congr 1
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, ← pow_mul, Nat.mul_comm]

/-- 同じ反復 Frobenius は実際の Proj の標準開の切断の p^e 乗に一致する。 -/
theorem projectiveProjNativeChart_iteratedFrobenius (T : Finset ι) (e : ℕ)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    (Proj.awayToSection G (algebraMap (MvPolynomial ι R) A
      (projectiveLaurentDenominator R T))).hom
      (projectiveHomogeneousChartLinearEquiv G T
        (projectiveChartIteratedFrobenius G p hp hR hA T e z)) =
    ((Proj.awayToSection G (algebraMap (MvPolynomial ι R) A
      (projectiveLaurentDenominator R T))).hom
      (projectiveHomogeneousChartLinearEquiv G T z)) ^ (p ^ e) := by
  rw [projectiveHomogeneousChartLinearEquiv_iteratedFrobenius, map_pow]

end SerrePositivity.AlgebraicGeometry
