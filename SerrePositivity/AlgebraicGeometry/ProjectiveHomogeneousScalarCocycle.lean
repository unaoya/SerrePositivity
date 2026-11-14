module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0PairEvaluation
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterAdd

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance projectiveScalarCocycleGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 適合切断代数の基底スカラーは、各標準開で同じ基底スカラー。 -/
theorem projectiveHomogeneousSectionAlgebra_algebraMap_apply (r : R) (t : Fin 1 → ι) :
    (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G) r).val t =
      algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj
        (cechTupleSupport t)) r := rfl

/-- 有限段のスカラーの Čech H⁰ 類の零次コサイクルは、各標準開で同じスカラー。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveHomogeneousScalarCechIntH0_cocycle (r : R) (t : Fin 1 → ι) :
    ((fullCechH0KernelIso (algebraCechIntDiagram
      (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G))).hom.hom
        (fullAlgebraCechIntH0Equiv (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)
          (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G) r))).val t =
      algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj
        (cechTupleSupport t)) r := by
  have h := fullAlgebraCechIntH0Equiv_kernel
    (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)
    (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G) r)
  exact congrArg (fun a ↦ a t) h

end SerrePositivity.AlgebraicGeometry
