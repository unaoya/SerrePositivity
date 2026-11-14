module

public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousTransition

/-!
概要：閉厚化の切断代数の遷移を Rees の Čech H⁰ の遷移と比較する。
方針：斉次局所化の遷移の自然性を切断代数と H⁰ へ送り、既存の商の比較を合成する。
規約：すべて実際の商環の因子写像から誘導する。
使われ方：閉厚化の切断代数への像の安定化の移送。
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
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance reesHomogeneousSectionTransitionGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 閉厚化の間の実際の切断代数の遷移。 -/
def reesClosedHomogeneousSectionTransition (i j : ℕ) (h : j ≤ i) :
    projectiveHomogeneousSectionAlgebra (ι := ι) ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) →ₐ[R]
      projectiveHomogeneousSectionAlgebra (ι := ι) ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G)) :=
  fullAlgebraCechEqualizerMap (reesClosedHomogeneousAlgebraTransition I G i j h)

/-- 切断代数の遷移の成分は、実際の標準開の環の遷移。 -/
theorem reesClosedHomogeneousSectionTransition_apply (i j : ℕ) (h : j ≤ i)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))) (t : Fin 1 → ι) :
    (reesClosedHomogeneousSectionTransition I G i j h a).val t =
      reesClosedHomogeneousChartTransition I G i j h (cechTupleSupport t) (a.val t) :=
  reesClosedHomogeneousModuleTransition_apply I G i j h (cechTupleSupport t) (a.val t)

/-- 切断代数の遷移は、元の次数付き加群の Čech H⁰ の遷移と可換。 -/
theorem projectiveHomogeneousSectionNatH0Equiv_transition (i j : ℕ) (h : j ≤ i)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))) :
    projectiveHomogeneousSectionNatH0Equiv ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G))
        (reesClosedHomogeneousSectionTransition I G i j h a) =
      (HomologicalComplex.homologyMap
        (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G i j h 0)) 0).hom
        (projectiveHomogeneousSectionNatH0Equiv ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) a) := by
  let H := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0
  have he : H.map (reesClosedHomogeneousModuleTransition I G i j h) ≫
      H.map (projectiveHomogeneousChartDiagramIso ((projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G))).inv =
      H.map (projectiveHomogeneousChartDiagramIso ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))).inv ≫
        H.map (reesClosedRingTransitionChartMap (ι := ι) I G i j h 0) := by
    rw [← H.map_comp, ← H.map_comp]
    simp only [reesClosedHomogeneousModuleTransition, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hn := fullAlgebraCechH0Equiv_naturality
    (reesClosedHomogeneousAlgebraTransition I G i j h) a
  exact (congrArg (H.map (projectiveHomogeneousChartDiagramIso
    (projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G)).inv).hom hn).trans
      (congrArg (fun f ↦ f.hom (projectiveHomogeneousSectionH0Equiv
        (projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G) a)) he)

/-- 切断代数の遷移は、像の安定化に用いた Rees の Čech H⁰ の遷移と可換。 -/
theorem reesClosedHomogeneousSectionH0Equiv_transition (i j : ℕ) (h : j ≤ i)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G))) :
    reesClosedHomogeneousSectionH0Equiv G I j
        (reesClosedHomogeneousSectionTransition I G i j h a) =
      (reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h 0 0).hom
        (reesClosedHomogeneousSectionH0Equiv G I i a) := by
  apply (reesClosedRingCechIso (ι := ι) I G j 0 0).toLinearEquiv.injective
  change (reesClosedRingCechIso (ι := ι) I G j 0 0).toLinearEquiv
    ((reesClosedRingCechIso (ι := ι) I G j 0 0).toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  have he := congrArg (fun f ↦ f.hom (reesClosedHomogeneousSectionH0Equiv G I i a))
    (reesClosedRingCechIso_transition (ι := ι) I G i j h 0 0)
  have hx : (reesClosedRingCechIso (ι := ι) I G i 0 0).hom.hom
      (reesClosedHomogeneousSectionH0Equiv G I i a) =
        projectiveHomogeneousSectionNatH0Equiv ((projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)) a :=
    (reesClosedRingCechIso (ι := ι) I G i 0 0).toLinearEquiv.apply_symm_apply _
  have he' : (reesClosedRingCechIso (ι := ι) I G j 0 0).hom.hom
      ((reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h 0 0).hom
        (reesClosedHomogeneousSectionH0Equiv G I i a)) =
      (HomologicalComplex.homologyMap
        (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G i j h 0)) 0).hom
        ((reesClosedRingCechIso (ι := ι) I G i 0 0).hom.hom
          (reesClosedHomogeneousSectionH0Equiv G I i a)) := he
  exact (projectiveHomogeneousSectionNatH0Equiv_transition I G i j h a).trans
    ((congrArg (HomologicalComplex.homologyMap
      (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G i j h 0)) 0).hom hx).symm.trans
        he'.symm)

end SerrePositivity.AlgebraicGeometry
