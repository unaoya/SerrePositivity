module

public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeCoefficient
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfCechCenterAugmentation
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeScalar
public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectChartMap
public import SerrePositivity.AlgebraicGeometry.FullCechComplexHomExt
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIsoNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback

/-!
概要：実際の Cartesian な閉厚化への制限と、Frobenius 係数の比較の自然性。
方針：非空交叉の環の同型を順極限へ送り、逆像と交叉の比較を合成する。
規約：次数付き商の Proj と pullback のスキームの同一視は使わない。
使われ方：F8 の閉厚化の複体を canonical な実際の基底変更へ接続する。
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
local instance closedPerfectNativeCenterGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 閉厚化の環の比較は、元の基底環の実際のスカラーに線形。 -/
theorem reesClosedNativeSectionRingIso_scalar (T : Finset ι) (hT : T.Nonempty) (r : R) :
    (reesClosedNativeSectionRingIso I G n iY g H T hT).hom.hom
        (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι)
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).obj T) r) =
      (Y.presheaf.map (homOfLE (show
        g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) T ≤ ⊤ from le_top)).op).hom
        (g.appTop.hom (projectiveScalarToGlobalSections G r)) := by
  have h := (reesClosedNativeSectionLinearEquiv I G n iY g H T hT).map_smul r
    (1 : HomogeneousLocalization.Away
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ n).map (algebraMap R A))
        (projectiveLaurentDenominator R T)))
  change (reesClosedNativeSectionRingIso I G n iY g H T hT).hom.hom (r • 1) =
    (Y.presheaf.map (homOfLE (show
      g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) T ≤ ⊤ from le_top)).op).hom
        (g.appTop.hom (projectiveScalarToGlobalSections G r)) *
      (reesClosedNativeSectionRingIso I G n iY g H T hT).hom.hom 1 at h
  rw [map_one, mul_one] at h
  convert h using 1
  congr 1

end SerrePositivity.AlgebraicGeometry
