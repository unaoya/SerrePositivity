module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartFractions
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap

/-!
概要：次数零の加群の写像と、斉次局所化の実際の環の写像を照合する。
方針：一つの斉次分数に戻し、係数の環の写像を分子に適用する。
規約：多項式環の作用を保つ環の写像と次数を保つことを明示する。
使われ方：閉厚化と模型の遷移を、実際の Proj の引き戻しにつなぐ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory HomogeneousLocalization
universe u
variable {R S A : Type u} {ι : Type} [CommRing R] [CommRing S] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R S) (H : ℕ → Submodule R A) [GradedRing G] [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : G →+*ᵍ H) (g : S →ₐ[MvPolynomial ι R] A)
variable (hfg : ∀ x, f x = g x)

include hfg in
/-- 多項式環上の写像は、標準開の分母の像を保つ。 -/
theorem projectiveHomogeneousRingChartMap_denominator (T : Finset ι) :
    f (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) =
      algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T) := by
  rw [hfg, g.commutes]

include hfg in
/-- 標準開の分母の冪の部分モノイドは、係数環の写像で次の段へ移る。 -/
theorem projectiveHomogeneousRingChartMap_powers (T : Finset ι) :
    Submonoid.powers (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) ≤
      (Submonoid.powers (algebraMap (MvPolynomial ι R) A
        (projectiveLaurentDenominator R T))).comap f.toRingHom := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  change _ = f (_ ^ n)
  rw [map_pow, projectiveHomogeneousRingChartMap_denominator G H f g hfg T]

/-- 斉次局所化の写像は、分子に係数の写像を適用し分母の指数を保つ。 -/
theorem projectiveHomogeneousRingChartMap_fraction (T : Finset ι) (n : ℕ)
    (m : S) (hm : m ∈ G (n • T.card)) :
    HomogeneousLocalization.map f (projectiveHomogeneousRingChartMap_powers G H f g hfg T)
      (Away.mk G (projectivePolynomialDenominatorImage_mem G T) n m hm) =
    Away.mk H (projectivePolynomialDenominatorImage_mem H T) n (g m)
      (by rw [← hfg]; exact f.2 hm) := by
  change HomogeneousLocalization.map f _ (HomogeneousLocalization.mk _) = HomogeneousLocalization.mk _
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  · exact hfg m
  · apply Subtype.ext
    change f (_ ^ n) = _ ^ n
    rw [map_pow, projectiveHomogeneousRingChartMap_denominator G H f g hfg T]

/-- 次数零の加群の写像は、実際の斉次局所化の環の写像と一致する。 -/
theorem projectiveHomogeneousChartLinearEquiv_map (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    projectiveHomogeneousChartLinearEquiv H T
        (((projectiveNatGradedModuleChartMap G H g.toLinearMap
          (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0).app T).hom z) =
      HomogeneousLocalization.map f (projectiveHomogeneousRingChartMap_powers G H f g hfg T)
        (projectiveHomogeneousChartLinearEquiv G T z) := by
  obtain ⟨n, m, hm, hfrac⟩ := Away.mk_surjective G
    (projectivePolynomialDenominatorImage_mem G T) (projectiveHomogeneousChartLinearEquiv G T z)
  have hz := projectiveHomogeneousChartLinearEquiv_fraction_reflect G T n m hm z hfrac.symm
  let z' := (((projectiveNatGradedModuleChartMap G H g.toLinearMap
    (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0).app T).hom z)
  have hm' : g m ∈ H (n • T.card) := by rw [← hfg]; exact f.2 hm
  have hz' : z'.val = LocalizedModule.mk (g m)
      (projDenominator (projectiveLaurentDenominator R T) n) := by
    change IsLocalizedModule.map (Submonoid.powers (projectiveLaurentDenominator R T))
      (LocalizedModule.mkLinearMap _ S) (LocalizedModule.mkLinearMap _ A) g.toLinearMap z.val = _
    rw [hz]
    exact IsLocalizedModule.map_LocalizedModules _ g.toLinearMap m _
  calc
    _ = Away.mk H (projectivePolynomialDenominatorImage_mem H T) n (g m) hm' :=
      projectiveHomogeneousChartLinearEquiv_fraction H T n (g m) hm' z' hz'
    _ = HomogeneousLocalization.map f
        (projectiveHomogeneousRingChartMap_powers G H f g hfg T)
        (Away.mk G (projectivePolynomialDenominatorImage_mem G T) n m hm) :=
      (projectiveHomogeneousRingChartMap_fraction G H f g hfg T n m hm).symm
    _ = _ := congrArg _ hfrac

end SerrePositivity.AlgebraicGeometry
