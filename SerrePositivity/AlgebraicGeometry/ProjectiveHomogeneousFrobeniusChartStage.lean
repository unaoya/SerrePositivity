module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusH0
public import SerrePositivity.AlgebraicGeometry.ProjectiveChartFrobeniusRingStage

/-!
概要：斉次標準開の係数順極限と実際の標準開環の比較の標準写像を明示する。
方針：多項式係数との比較を打ち消し、各標準開の Frobenius 標準写像へ戻す。
規約：複体の比較は既存の projectiveHomogeneousFrobeniusRingCechIso と同じ。
使われ方：零次コサイクルでの増大写像の計算。
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

/-- 実際の標準開環と、斉次代数係数の順極限との係数図式の比較。 -/
def projectiveHomogeneousFrobeniusChartColimitIso :
    projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA ≅
      colimit (algebraCechFrobeniusCoefficientFunctor
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR) :=
  (projectiveFrobeniusRingChartDiagramIso (ι := ι) G p hp hR hA).symm ≪≫
    colim.mapIso (projectiveHomogeneousFrobeniusCoefficientIso G p hp hR hA)

/-- 既存の複体比較の逆は係数図式の比較の逆から誘導される。 -/
theorem projectiveHomogeneousFrobeniusRingCechIso_inv :
    (projectiveHomogeneousFrobeniusRingCechIso (ι := ι) G p hp hR hA).inv =
      fullCechComplexMap
        (projectiveHomogeneousFrobeniusChartColimitIso (ι := ι) G p hp hR hA).inv := by
  change (fullCechComplexFunctor (R := ℤ) (ι := ι)).map _ ≫
    (fullCechComplexFunctor (R := ℤ) (ι := ι)).map _ = _
  rw [← Functor.map_comp]
  rfl

/-- 斉次代数係数の有限段の元は、実際の標準開環の同じ Frobenius 標準元に移る。 -/
theorem projectiveHomogeneousFrobeniusChartColimitIso_stage
    (T : Finset ι) (n : ℕ)
    (x : (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T) :
    ((projectiveHomogeneousFrobeniusChartColimitIso (ι := ι) G p hp hR hA).inv.app T).hom
      (((colimit.ι (algebraCechFrobeniusCoefficientFunctor
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR) n).app T).hom x) =
    frobeniusDirectLimitOf _ p hp (projectiveHomogeneousChart_primeCast G p hR T) n x := by
  have h := congrArg (fun η ↦ (η.app T).hom x)
    (colimit.ι_map (projectiveHomogeneousFrobeniusCoefficientIso G p hp hR hA).inv n)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  let e := projectiveChartFrobeniusRingColimitIso G p hp hR hA T
  have hh := congrArg (fun z ↦ e.hom.hom z) h
  refine hh.trans ?_
  have hs := projectiveChartFrobeniusRingColimitIso_stage G p hp hR hA T n
    ((projectiveHomogeneousChartLinearEquiv G T).symm x)
  exact hs.trans (congrArg
    (frobeniusDirectLimitOf _ p hp (projectiveHomogeneousChart_primeCast G p hR T) n)
    ((projectiveHomogeneousChartLinearEquiv G T).apply_symm_apply x))

end SerrePositivity.AlgebraicGeometry
