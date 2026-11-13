module

public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousSections

/-!
概要：斉次標準開の切断代数を、Rees の評価に用いた Čech H⁰ の表示へ戻す。
方針：標準開の比較と環の商の比較を合成し、閉厚化への制限の可換性を保つ。
規約：同型は既存の係数図式の同型から誘導する。
使われ方：核・像の評価を実際の切断代数の制限へ移す。
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

/-- 切断代数を、元の次数付き加群で計算した Čech H⁰ と比較する。 -/
def projectiveHomogeneousSectionNatH0Equiv :
    projectiveHomogeneousSectionAlgebra (ι := ι) G ≃ₗ[R]
      (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G 0)).homology 0 :=
  (projectiveHomogeneousSectionH0Equiv (ι := ι) G).trans
    (((fullCechComplexFunctor ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0).mapIso
        (projectiveHomogeneousChartDiagramIso (ι := ι) G)).symm.toLinearEquiv)

variable (I : Ideal R)
local instance reesSectionComparisonGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 切断代数と次数付き加群の H⁰ の比較は、閉厚化への実際の制限と可換。 -/
theorem projectiveHomogeneousSectionNatH0Equiv_projection (n : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) :
    projectiveHomogeneousSectionNatH0Equiv
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
        (reesClosedHomogeneousSectionProjection G I n a) =
      (HomologicalComplex.homologyMap
        (fullCechComplexMap (reesClosedRingProjectionChartMap (ι := ι) I G n 0)) 0).hom
        (projectiveHomogeneousSectionNatH0Equiv G a) := by
  let H := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0
  have he : H.map (reesClosedHomogeneousModuleProjection I G n) ≫
      H.map (projectiveHomogeneousChartDiagramIso
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).inv =
      H.map (projectiveHomogeneousChartDiagramIso G).inv ≫
        H.map (reesClosedRingProjectionChartMap (ι := ι) I G n 0) := by
    rw [← H.map_comp, ← H.map_comp]
    simp only [reesClosedHomogeneousModuleProjection, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  change (H.map (projectiveHomogeneousChartDiagramIso _).inv).hom
      (projectiveHomogeneousSectionH0Equiv _
        (reesClosedHomogeneousSectionProjection G I n a)) = _
  rw [reesClosedHomogeneousSectionH0Equiv_projection]
  exact congrArg (fun f ↦ f.hom (projectiveHomogeneousSectionH0Equiv G a)) he

/-- 閉厚化の切断代数を、Rees の商加群の Čech H⁰ と比較する。 -/
def reesClosedHomogeneousSectionH0Equiv (n : ℕ) :
    projectiveHomogeneousSectionAlgebra (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) ≃ₗ[R]
      reesAdicProjectiveClosedCechHomology (ι := ι) I G n 0 0 :=
  (projectiveHomogeneousSectionNatH0Equiv
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).trans
      (reesClosedRingCechIso (ι := ι) I G n 0 0).symm.toLinearEquiv

/-- Rees の商との比較は、切断代数の制限を元の閉厚化への H⁰ の射へ送る。 -/
theorem reesClosedHomogeneousSectionH0Equiv_reesProjection (n : ℕ)
    (a : projectiveHomogeneousSectionAlgebra (ι := ι) G) :
    reesClosedHomogeneousSectionH0Equiv G I n
        (reesClosedHomogeneousSectionProjection G I n a) =
      (reesAdicProjectiveClosedCechProjection (ι := ι) I G n 0 0).hom
        (projectiveHomogeneousSectionNatH0Equiv G a) := by
  apply (reesClosedRingCechIso (ι := ι) I G n 0 0).toLinearEquiv.injective
  change (reesClosedRingCechIso (ι := ι) I G n 0 0).toLinearEquiv
    ((reesClosedRingCechIso (ι := ι) I G n 0 0).toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (projectiveHomogeneousSectionNatH0Equiv_projection G I n a).trans
    ((congrArg (fun f ↦ f.hom (projectiveHomogeneousSectionNatH0Equiv G a))
    (reesClosedRingCechIso_projection (ι := ι) I G n 0 0)).symm)

end SerrePositivity.AlgebraicGeometry
