module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousClosedCenterExact

/-!
概要：閉厚化の完全列の差写像を、元の切断の制限の差として照合する。
方針：Frobenius 順極限の有限段で商の因子化を評価する。
規約：射影側の辺は実際の閉厚化への切断の制限。
使われ方：F7 と Čech H⁰ の自然な比較で、同じ四角形の写像を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
private theorem ringHom_map_sub_explicit {B C : Type u} [CommRing B] [CommRing C]
    (f : B →+* C) (x y : B) : f (x - y) = f x - f y := map_sub f x y
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
local instance homogeneousClosedCenterMapsGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 基底の中心の環から閉厚化の適合切断への実際の環準同型。 -/
def projectiveHomogeneousClosedCenterBaseMap :
    R ⧸ (I ^ 1) →+* projectiveHomogeneousSectionAlgebra (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) :=
  (reesClosedHomogeneousSectionQuotientMap G I 1).comp
    (Ideal.quotientMap ((I ^ 1).map (algebraMap R
      (projectiveHomogeneousSectionAlgebra (ι := ι) G)))
      (algebraMap R (projectiveHomogeneousSectionAlgebra (ι := ι) G)) Ideal.le_comap_map)

/-- 基底の中心の元の代表元は、閉厚化の切断の同じスカラーへ送られる。 -/
theorem projectiveHomogeneousClosedCenterBaseMap_mk (r : R) :
    projectiveHomogeneousClosedCenterBaseMap (ι := ι) G I (Ideal.Quotient.mk (I ^ 1) r) =
      algebraMap R _ r :=
  (reesClosedHomogeneousSectionProjection G I 1).commutes r

/-- 完全列の差写像は、切断の実際の閉厚化への制限と基底の中心からの射の差。 -/
theorem projectiveHomogeneousClosedCenterDifference_apply
    (b : FrobeniusDirectLimit (projectiveHomogeneousSectionAlgebra (ι := ι) G) p hp
      (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR))
    (c : FrobeniusDirectLimit (R ⧸ (I ^ 1)) p hp
      (frobeniusQuotientPrimeCast p hR (I ^ 1))) :
    projectiveHomogeneousClosedCenterDifference (ι := ι) G I p hp hR (b, c) =
      frobeniusDirectLimitMap p hp
        (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)
        (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι)
          (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hR)
        (reesClosedHomogeneousSectionProjection G I 1).toRingHom b -
      frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))
        (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι)
          (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hR)
        (projectiveHomogeneousClosedCenterBaseMap (ι := ι) G I) c := by
  change projectiveHomogeneousClosedCenterComparison (ι := ι) G I p hp hR (_ - _) = _
  rw [ringHom_map_sub_explicit]
  congr 1
  · obtain ⟨n, b, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap _ p hp
        (projectiveHomogeneousSectionAlgebra_primeCast (ι := ι) G p hR)) b
    rfl
  · obtain ⟨n, c, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap _ p hp (frobeniusQuotientPrimeCast p hR (I ^ 1))) c
    rfl

end SerrePositivity.AlgebraicGeometry
