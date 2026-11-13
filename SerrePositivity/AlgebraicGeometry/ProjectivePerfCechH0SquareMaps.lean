module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0Square
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0Evaluation
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechH0CenterClass

/-!
概要：移送した Čech H⁰ の四角形の差を、実際の閉厚化の制限で表示する。
方針：切断環の差の式と、閉厚化の H⁰ 比較の自然性を合成する。
規約：右辺の制限は F6 の複体の射の H⁰。
使われ方：F8 の全複体の差写像と F7 の完全列の写像を揃える。
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
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
local instance perfCechH0SquareMapsGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- Čech H⁰ の差写像は、実際の閉厚化の制限と基底の中心からの写像の差。 -/
theorem projectivePerfCechH0Difference_apply
    (b : projectivePerfCechH0 (ι := ι) G p hp hR hA)
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    projectivePerfCechH0Difference (ι := ι) G I p hp hR hA (b, c) =
      (HomologicalComplex.homologyMap
        (reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1) 0).hom b -
      projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA c := by
  unfold projectivePerfCechH0Difference
  conv_lhs =>
    arg -1
    arg -1
    rw [projectivePerfCechH0CenterEquiv_apply (ι := ι) G I p hp hR hA b c]
  simp only [projectivePerfCechH0Equiv_symm_apply]
  conv_lhs =>
    arg -1
    rw [projectiveHomogeneousClosedCenterDifference_apply (ι := ι) G I p hp hR]
  rw [projectivePerfCechH0Iso_inv_sub (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))]
  have hc := congrArg (fun f ↦ f.hom b)
    (projectiveHomogeneousFrobeniusRingCechH0Iso_projection (ι := ι) I G p hp hR hA 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    AddMonoidHom.coe_toIntLinearMap, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass] at hc
  have hi := projectivePerfCechH0Iso_inv_eq (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) _ _ hc
  convert congrArg (fun (x : projectivePerfCechH0 (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A)))) ↦
    x - projectivePerfCechH0CenterClass (ι := ι) G I p hp hR hA c) hi using 1 <;>
    simp only [projectivePerfCechH0CenterClass]

end SerrePositivity.AlgebraicGeometry
