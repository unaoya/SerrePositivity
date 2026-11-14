module

public import SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRingColimit

/-!
概要：標準開の Frobenius 順極限比較を各段からの標準写像と照合する。
方針：評価関手の余極限比較、系の自然同型、環の順極限比較を合成する。
規約：実際の斉次局所化の環の標準元を用いる。
使われ方：Čech H⁰ の零次コサイクルを標準開上で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 各標準開の比較に有限段から入る射は、環の系の同じ標準写像である。 -/
theorem projectiveChartFrobeniusRingColimitIso_ι (T : Finset ι) (n : ℕ) :
    ((colimit.ι (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA) n).app T) ≫
      (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).hom =
    ((projectiveChartFrobeniusRingSystemIso G p hp hR hA T).app n).hom ≫
      colimit.ι (projectiveChartRingFrobeniusFunctor G p hp hR T) n ≫
      (ringDirectLimitIntColimitIso
        (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T))).inv := by
  simp only [projectiveChartFrobeniusRingColimitIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  change ((evaluation (Finset ι) (ModuleCat.{u} ℤ)).obj T).map
      (colimit.ι (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA) n) ≫ _ = _
  rw [← Category.assoc, ι_preservesColimitIso_hom, colimit.ι_map_assoc]
  rfl

/-- 有限段の元は実際の斉次局所化の環の同じ Frobenius 標準元へ移る。 -/
theorem projectiveChartFrobeniusRingColimitIso_stage (T : Finset ι) (n : ℕ)
    (x : ((projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA).obj n).obj T) :
    (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).hom.hom
      (((colimit.ι (projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA) n).app T).hom x) =
    frobeniusDirectLimitOf _ p hp (projectiveHomogeneousChart_primeCast G p hR T) n
      (projectiveHomogeneousChartLinearEquiv G T x) := by
  have h := congrArg (fun f ↦ f.hom x)
    (projectiveChartFrobeniusRingColimitIso_ι G p hp hR hA T n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  let f := frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T)
  let e := ringDirectLimitIntColimitIso f
  have he := congrArg (fun z ↦ e.inv.hom z)
    (ringDirectLimitIntColimitIso_of f n (projectiveHomogeneousChartLinearEquiv G T x)).symm
  exact h.trans (he.trans (e.toLinearEquiv.symm_apply_apply _))

end SerrePositivity.AlgebraicGeometry
