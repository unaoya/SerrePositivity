module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedPresentation
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizationMaps
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：次数を保つ短完全列は、標準開の狭義増加 Čech 複体の短完全列を与える。
方針：各次数の完全性を局所化し、有限交叉の項ごとの短完全列を Čech 関手へ送る。
規約：三つの加群に次数分解を与える。
使われ方：有限斉次自由表示からコホモロジーの長完全列を作る。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

universe u

variable {ι R : Type*} [LinearOrder ι] [Fintype ι] [CommRing R]
variable {M N P : Type u}
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) P]
variable (G : ℤ → Submodule R M) (H : ℤ → Submodule R N) (J : ℤ → Submodule R P)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H] [DirectSum.Decomposition J]
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) G]
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) H]
variable [SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))) J]

/-- 斉次な短完全列は標準開の Čech 複体でも短完全となる。 -/
theorem projectiveOrderedCech_shortExact (d : ℤ)
    (f : M →ₗ[MvPolynomial ι R] N) (g : N →ₗ[MvPolynomial ι R] P)
    (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n) (hg : ∀ n, ∀ m ∈ H n, g m ∈ J n)
    (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g) :
    ∃ hzero :
        projectiveGradedModuleChartMap (ι := ι) G H d f hf ≫
          projectiveGradedModuleChartMap (ι := ι) H J d g hg = 0,
      ((ShortComplex.mk (projectiveGradedModuleChartMap (ι := ι) G H d f hf)
        (projectiveGradedModuleChartMap (ι := ι) H J d g hg) hzero).map
          (orderedCechComplexFunctor (R := R) (ι := ι))).ShortExact := by
  let p := projectiveGradedModuleChartMap (ι := ι) G H d f hf
  let q := projectiveGradedModuleChartMap (ι := ι) H J d g hg
  have hT (T : Finset ι) : Function.Exact (p.app T).hom (q.app T).hom := by
    change Function.Exact
      (projectiveGradedAwayMap (projectiveLaurentDenominator R T)
        (fun n ↦ G (d + n • (T.card : ℤ))) (fun n ↦ H (d + n • (T.card : ℤ))) f
        (fun n ↦ hf (d + n • (T.card : ℤ))))
      (projectiveGradedAwayMap (projectiveLaurentDenominator R T)
        (fun n ↦ H (d + n • (T.card : ℤ))) (fun n ↦ J (d + n • (T.card : ℤ))) g
        (fun n ↦ hg (d + n • (T.card : ℤ))))
    exact projectiveGradedAwayMap_exact _ _ _ _ f g
      (fun n ↦ hf (d + n • (T.card : ℤ)))
      (fun n ↦ hg (d + n • (T.card : ℤ)))
      (projectiveGradedChart_mul_denominator (ι := ι) G T d)
      (projectiveGradedChart_mul_denominator (ι := ι) H T d)
      (fun n y ↦ projectiveGradedMap_exact_piece G H f g hf hex
        (d + n • (T.card : ℤ)) y)
  have hzero : p ≫ q = 0 := by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change (q.app T).hom ((p.app T).hom y) = 0
    exact (hT T _).mpr ⟨y, rfl⟩
  refine ⟨hzero, orderedCechComplex_shortExact p q hzero ?_⟩
  intro T
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (hT T)
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact projectiveGradedAwayMap_injective _ _ _ f
      (fun n ↦ hf (d + n • (T.card : ℤ))) hinj
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact projectiveGradedAwayMap_surjective _ _ _ g
      (fun n ↦ hg (d + n • (T.card : ℤ)))
      (projectiveGradedChart_mul_denominator (ι := ι) J T d)
      (fun n y ↦ projectiveGradedMap_surjective_piece H J g hg hsurj
        (d + n • (T.card : ℤ)) y)

end SerrePositivity.AlgebraicGeometry
