module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFullGradedCechExact

/-!
概要：自然数次数の短完全列を、全タプル Čech 複体の短完全列にする。
方針：三つの次数を整数へ延ばし、斉次局所化の完全性を使う。
規約：写像は多項式環上線形で次数を保つ。
使われ方：I 進閉厚化の Čech 長完全列を作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M N P : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) P]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N) (J : ℕ → Submodule R P)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H] [DirectSum.Decomposition J]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) J]

/-- 自然数次数を保つ短完全列は、全タプル標準開 Čech 複体でも短完全。 -/
theorem projectiveNatFullCech_shortExact (d : ℤ)
    (f : M →ₗ[MvPolynomial ι R] N) (g : N →ₗ[MvPolynomial ι R] P)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) (hg : ∀ n, ∀ m ∈ H n, g m ∈ J n)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g) :
    ∃ hzero : projectiveNatGradedModuleChartMap (ι := ι) G H f hf d ≫
        projectiveNatGradedModuleChartMap (ι := ι) H J g hg d = 0,
      ((ShortComplex.mk (projectiveNatGradedModuleChartMap (ι := ι) G H f hf d)
        (projectiveNatGradedModuleChartMap (ι := ι) H J g hg d) hzero).map
          (fullCechComplexFunctor (R := R) (ι := ι))).ShortExact := by
  letI := projectiveNatGradingIntDecomposition G
  letI := projectiveNatGradingIntDecomposition H
  letI := projectiveNatGradingIntDecomposition J
  letI := projectiveNatGradingIntSMul (ι := ι) G
  letI := projectiveNatGradingIntSMul (ι := ι) H
  letI := projectiveNatGradingIntSMul (ι := ι) J
  exact projectiveFullCech_shortExact (ι := ι)
    (projectiveNatGradingInt G) (projectiveNatGradingInt H) (projectiveNatGradingInt J)
    d f g (projectiveNatGradingInt_map_mem G H f hf)
      (projectiveNatGradingInt_map_mem H J g hg) hinj hex hsurj

end SerrePositivity.AlgebraicGeometry
