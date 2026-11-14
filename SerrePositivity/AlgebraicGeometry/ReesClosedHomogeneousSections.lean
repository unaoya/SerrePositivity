module

public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousAlgebraProjection

/-!
概要：閉厚化への標準開環の制限を、適合切断環と Čech H⁰ の同じ写像へ送る。
方針：代数係数図式の自然変換に、適合切断環の関手と H⁰ の自然性を適用する。
規約：部分代数の積は実際の斉次局所化の積。
使われ方：F7 の閉厚化比較に、2e の線形な核の評価と像の安定化を移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 斉次標準開の実際の環の適合する切断の部分代数。 -/
abbrev projectiveHomogeneousSectionAlgebra :=
  fullAlgebraCechEqualizer (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)

/-- 斉次標準開の切断代数と Čech H⁰ の線形比較。BST13 Lemma 3.8 の H⁰ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveHomogeneousSectionH0Equiv :
    projectiveHomogeneousSectionAlgebra (ι := ι) G ≃ₗ[R]
      (fullCechComplex (projectiveHomogeneousChartDiagram (ι := ι) G)).homology 0 :=
  fullAlgebraCechH0Equiv (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)

/-- 射影有限性から、斉次標準開の適合切断の部分代数は基底環上有限。 -/
theorem projectiveHomogeneousSectionAlgebra_finite
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A] :
    Module.Finite R (projectiveHomogeneousSectionAlgebra (ι := ι) G) := by
  letI := projectiveHomogeneousChartFullCechHomology_finite (ι := ι) G 0
  exact Module.Finite.of_surjective (projectiveHomogeneousSectionH0Equiv (ι := ι) G).symm.toLinearMap
    (projectiveHomogeneousSectionH0Equiv (ι := ι) G).symm.surjective

variable (I : Ideal R)
local instance reesHomogeneousSectionsGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化の斉次標準開の適合切断代数への実際の制限。 -/
def reesClosedHomogeneousSectionProjection (n : ℕ) :
    projectiveHomogeneousSectionAlgebra (ι := ι) G →ₐ[R]
      projectiveHomogeneousSectionAlgebra (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  fullAlgebraCechEqualizerMap (reesClosedHomogeneousAlgebraProjection I G n)

/-- 切断代数の制限の各成分は、閉厚化への斉次局所化の環の射影。 -/
theorem reesClosedHomogeneousSectionProjection_apply (n : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) (t : Fin 1 → ι) :
    (reesClosedHomogeneousSectionProjection G I n a).val t =
      reesClosedHomogeneousChartProjection I G n (cechTupleSupport t) (a.val t) :=
  reesClosedHomogeneousModuleProjection_apply I G n (cechTupleSupport t) (a.val t)

/-- 切断環の実際の制限は、同じ係数写像から作る Čech H⁰ の写像と可換。 -/
theorem reesClosedHomogeneousSectionH0Equiv_projection (n : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) :
    projectiveHomogeneousSectionH0Equiv
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
        (reesClosedHomogeneousSectionProjection G I n a) =
      (HomologicalComplex.homologyMap
        (fullCechComplexMap (reesClosedHomogeneousModuleProjection I G n)) 0).hom
        (projectiveHomogeneousSectionH0Equiv G a) :=
  fullAlgebraCechH0Equiv_naturality (reesClosedHomogeneousAlgebraProjection I G n) a

end SerrePositivity.AlgebraicGeometry
