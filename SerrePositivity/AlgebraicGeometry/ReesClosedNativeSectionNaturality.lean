module

public import SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionRingIso

/-!
概要：実際の Cartesian な閉厚化の切断との環の同型を、非空交叉の制限に自然にする。
方針：2e の三つの係数比較の自然性を合成し、同じ環の写像に読む。
規約：空交叉の環の同型は使わない。
使われ方：F8 の閉厚化の Frobenius 係数を、実際の被覆の複体へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (n : ℕ)
local instance closedNativeSectionNaturalityGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 商の斉次局所化から実際の切断への線形比較は、非空交叉の制限と可換。 -/
theorem reesClosedNativeSectionLinearEquiv_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveHomogeneousChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).map (homOfLE h) ≫
        (reesClosedNativeSectionLinearEquiv I G n iY g H U (hT.mono h)).toModuleIso.hom =
      (reesClosedNativeSectionLinearEquiv I G n iY g H T hT).toModuleIso.hom ≫
        (openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
          (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h) := by
  let η := (projectiveHomogeneousChartDiagramIso (ι := ι)
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).inv ≫
      (reesClosedRingChartIso (ι := ι) I G n 0).inv
  change _ ≫ (η.app U ≫ (reesAdicNativeClosedCoefficientIso I G n iY g H U (hT.mono h)).hom) =
    (η.app T ≫ (reesAdicNativeClosedCoefficientIso I G n iY g H T hT).hom) ≫ _
  rw [← Category.assoc, η.naturality (homOfLE h), Category.assoc,
    reesAdicNativeClosedCoefficientIso_naturality I G n iY g H hT h]
  simp only [Category.assoc]

/-- 同じ環の同型は、実際の閉厚化の切断環の制限と可換。 -/
theorem reesClosedNativeSectionRingIso_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U)
    (x : (projectiveHomogeneousChartDiagram
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).obj T) :
    (reesClosedNativeSectionRingIso I G n iY g H U (hT.mono h)).hom.hom
        (((algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G))).map (homOfLE h)).hom x) =
      (Y.presheaf.map
        ((Opens.map g.base).map
          (homOfLE (cechOpenIntersection_antitone (projectiveProjCechOpen G) h))).op).hom
        ((reesClosedNativeSectionRingIso I G n iY g H T hT).hom.hom x) :=
  congrArg (fun m ↦ m.hom x) (reesClosedNativeSectionLinearEquiv_naturality I G n iY g H hT h)

end SerrePositivity.AlgebraicGeometry
