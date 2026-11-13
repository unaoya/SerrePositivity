module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0ColimitNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusRingChartDiagram
public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSections

/-!
概要：F6 の実際の標準開環の複体の H⁰ を、斉次切断環の Frobenius 順極限と比較する。
方針：多項式加群の係数系と斉次局所化の係数系を実際の Frobenius に沿って同定する。
規約：F6 と同じ projectiveFrobeniusRingChartDiagram を使う。
使われ方：F7 の短完全列の H⁰ を、F8 の正次数の計算と同じ複体へ置く。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 多項式加群と斉次標準開の係数 Frobenius 系の自然同型。 -/
def projectiveHomogeneousFrobeniusCoefficientIso :
    projectiveCechFrobeniusCoefficientFunctor (ι := ι) G p hp hR hA ≅
      algebraCechFrobeniusCoefficientFunctor
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR :=
  NatIso.ofComponents (fun _ ↦ isoWhiskerRight
    (projectiveHomogeneousChartDiagramIso (ι := ι) G)
    (ModuleCat.restrictScalars (Int.castRingHom R))) (by
      intro i j f
      apply NatTrans.ext
      funext T
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change projectiveHomogeneousChartLinearEquiv G T
        (projectiveChartIteratedFrobenius G p hp hR hA T (j - i) x) =
        frobeniusDirectSystemMap _ p hp _ i j (leOfHom f)
          (projectiveHomogeneousChartLinearEquiv G T x)
      rw [frobeniusDirectSystemMap_apply]
      exact projectiveHomogeneousChartLinearEquiv_iteratedFrobenius G p hp hR hA T (j - i) x)

/-- F6 の標準開環の複体と、斉次代数係数の Frobenius 順極限の複体の同型。 -/
def projectiveHomogeneousFrobeniusRingCechIso :
    fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA) ≅
      fullCechComplex (colimit (algebraCechFrobeniusCoefficientFunctor
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR)) :=
  (projectiveFrobeniusRingChartCechIso (ι := ι) G p hp hR hA).symm ≪≫
    fullCechComplexFunctor.mapIso
      (colim.mapIso (projectiveHomogeneousFrobeniusCoefficientIso G p hp hR hA))

/-- F6 と同じ標準開環の複体の Čech H⁰ と、切断環の Frobenius 順極限との同型。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveHomogeneousFrobeniusRingCechH0Iso :
    (fullCechComplex
      (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).homology 0 ≅
    ModuleCat.of ℤ (FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G)
      p hp (algebraCechEqualizer_primeCast
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hR)) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).mapIso
    (projectiveHomogeneousFrobeniusRingCechIso G p hp hR hA) ≪≫
      algebraCechFrobeniusH0ColimitIso
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR

end SerrePositivity.AlgebraicGeometry
