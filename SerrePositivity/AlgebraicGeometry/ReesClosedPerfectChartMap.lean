module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechMaps
public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusCanonicalProjection

/-!
概要：F8 の実際の閉厚化の射を、次数を保つ環の写像の一般構成と照合する。
方針：実際の次数付き商写像に一般構成を適用し、既存の canonical な比較を消去する。
規約：元の閉厚化への制限を別の写像で定義し直さない。
使われ方：native な複体比較の自然性を、F8 の同じ制限写像に適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor HomogeneousIdeal _root_.AlgebraicGeometry
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance closedPerfectChartGradedRing (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

/-- 実際の次数付き商は irrelevant ideal の条件を満たし、Proj の射を定める。 -/
theorem reesClosedGradedRingProjection_irrelevant (n : ℕ) :
    irrelevant (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) ≤
      (irrelevant G).map (reesClosedGradedRingProjection I G n) := by
  apply (irrelevant_le _).mpr
  intro i hi x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Ideal.mem_map_of_mem (reesClosedGradedRingProjection I G n).toRingHom
    (mem_irrelevant_of_mem G hi hy)

/-- 閉厚化の商の射は、環の係数図式の一般の写像と同じもの。 -/
theorem reesClosedHomogeneousRingDiagramMap_eq (n : ℕ) :
    projectiveHomogeneousRingDiagramMap G
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (reesClosedGradedRingProjection I G n)
      (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A)))
      (fun _ ↦ rfl) =
    whiskerRight (reesClosedHomogeneousAlgebraProjection (ι := ι) I G n)
      (forget₂ (CommAlgCat R) CommRingCat) := by
  ext T x
  exact (reesClosedHomogeneousModuleProjection_apply I G n T x).symm

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 一般の写像の構成は、F8 の実際の閉厚化の係数の制限を与える。 -/
theorem reesClosedPerfectChartMap_eq (n : ℕ) :
    projectivePerfectChartMap G
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (reesClosedGradedRingProjection I G n)
      (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A)))
      (fun _ ↦ rfl) p hp hR hA
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) =
        reesClosedFrobeniusRingChartMap (ι := ι) I G p hp hR hA n := by
  unfold projectivePerfectChartMap
  rw [reesClosedHomogeneousRingDiagramMap_eq]
  apply (cancel_mono (projectiveFrobeniusRingChartDiagram_isoCanonical (ι := ι)
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (reesClosedFrobeniusRingChartMap_canonical G I p hp hR hA n).symm

end SerrePositivity.AlgebraicGeometry
