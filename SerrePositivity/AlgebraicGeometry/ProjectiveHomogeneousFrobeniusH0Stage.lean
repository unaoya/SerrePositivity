module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0Stage
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousScalarCocycle

/-!
概要：実際の標準開環の Čech H⁰ の比較の逆を、有限段のスカラーから表示する。
方針：一般の代数係数の標準写像の公式を、F6 の複体との同型で移す。
規約：有限段の零次コサイクルは斉次標準開上のスカラーである。
使われ方：H⁰ の短完全列の左辺と Čech 増大写像との接続。
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

/-- 実際の標準開環の Čech H⁰ のスカラー類は、有限段のスカラー類の像である。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfCechH0ScalarClass_stage (n : ℕ) (r : R) :
    projectivePerfCechH0ScalarClass (ι := ι) G p hp hR hA
      (frobeniusDirectLimitOf R p hp hR n r) =
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
      (projectiveHomogeneousFrobeniusRingCechIso (ι := ι) G p hp hR hA).inv).hom
      (((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
        (fullCechComplexMap (colimit.ι (algebraCechFrobeniusCoefficientFunctor
          (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR) n))).hom
          (fullAlgebraCechIntH0Equiv
            (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)
            (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G) r))) := by
  rw [projectivePerfCechH0ScalarClass_of]
  change ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
    (projectiveHomogeneousFrobeniusRingCechIso (ι := ι) G p hp hR hA).inv).hom
      ((algebraCechFrobeniusH0ColimitIso
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR).inv.hom _) = _
  exact congrArg (fun x ↦
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0).map
      (projectiveHomogeneousFrobeniusRingCechIso (ι := ι) G p hp hR hA).inv).hom x)
    (algebraCechFrobeniusH0ColimitIso_inv_of
      (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR n
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G) r))

end SerrePositivity.AlgebraicGeometry
