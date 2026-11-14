module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatCechExact

/-!
概要：自然数次数の短完全列の、個々の標準開の指定次数部分での完全性を取り出す。
方針：負次数を零に延ばし、分子の各次数の完全性を局所化する。
規約：複体の全体だけでなく、非空交叉の係数ごとの結論を供給する。
使われ方：閉厚化の Rees の商と実際の切断の、同じ核による比較。
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
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]

include G H in
/-- 次数ごとに全射な加群の射は、各標準開の指定次数部分へも全射。 -/
theorem projectiveNatChartMap_surjective (f : M →ₗ[MvPolynomial ι R] N)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) (hs : Function.Surjective f) (d : ℤ) (T : Finset ι) :
    Function.Surjective (((projectiveNatGradedModuleChartMap G H f hf d).app T).hom) := by
  letI := projectiveNatGradingIntDecomposition G
  letI := projectiveNatGradingIntDecomposition H
  letI := projectiveNatGradingIntSMul (ι := ι) G
  letI := projectiveNatGradingIntSMul (ι := ι) H
  exact projectiveGradedAwayMap_surjective (projectiveLaurentDenominator R T)
    (fun n ↦ projectiveNatGradingInt G (d + n • (T.card : ℤ)))
    (fun n ↦ projectiveNatGradingInt H (d + n • (T.card : ℤ))) f
    (fun n ↦ projectiveNatGradingInt_map_mem G H f hf (d + n • (T.card : ℤ)))
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt H) T d)
    (fun n y ↦ projectiveGradedMap_surjective_piece (projectiveNatGradingInt G)
      (projectiveNatGradingInt H) f (projectiveNatGradingInt_map_mem G H f hf)
      hs (d + n • (T.card : ℤ)) y)

variable (K : ℕ → Submodule R P) [DirectSum.Decomposition K]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) K]

/-- 次数を保つ完全列は、各標準開の指定次数部分でも完全。 -/
theorem projectiveNatChartMap_exact (f : M →ₗ[MvPolynomial ι R] N)
    (g : N →ₗ[MvPolynomial ι R] P)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) (hg : ∀ n, ∀ m ∈ H n, g m ∈ K n)
    (he : Function.Exact f g) (d : ℤ) (T : Finset ι) :
    Function.Exact (((projectiveNatGradedModuleChartMap G H f hf d).app T).hom)
      (((projectiveNatGradedModuleChartMap H K g hg d).app T).hom) := by
  letI := projectiveNatGradingIntDecomposition G
  letI := projectiveNatGradingIntDecomposition H
  letI := projectiveNatGradingIntSMul (ι := ι) G
  letI := projectiveNatGradingIntSMul (ι := ι) H
  letI := projectiveNatGradingIntSMul (ι := ι) K
  exact projectiveGradedAwayMap_exact (projectiveLaurentDenominator R T)
    (fun n ↦ projectiveNatGradingInt G (d + n • (T.card : ℤ)))
    (fun n ↦ projectiveNatGradingInt H (d + n • (T.card : ℤ)))
    (fun n ↦ projectiveNatGradingInt K (d + n • (T.card : ℤ))) f g
    (fun n ↦ projectiveNatGradingInt_map_mem G H f hf (d + n • (T.card : ℤ)))
    (fun n ↦ projectiveNatGradingInt_map_mem H K g hg (d + n • (T.card : ℤ)))
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt G) T d)
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt H) T d)
    (fun n y ↦ projectiveGradedMap_exact_piece (projectiveNatGradingInt G)
      (projectiveNatGradingInt H) f g (projectiveNatGradingInt_map_mem G H f hf)
      he (d + n • (T.card : ℤ)) y)

end SerrePositivity.AlgebraicGeometry
