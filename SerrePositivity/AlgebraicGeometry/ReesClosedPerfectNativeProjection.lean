module

public import SerrePositivity.AlgebraicGeometry.ReesClosedPerfectNativeCoefficient
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
local instance closedPerfectNativeProjectionGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 実際の閉厚化への係数の制限は、同じ構造層の引き戻しに対応する。 -/
theorem reesClosedPerfectNativePushedCoefficientIso_projection
    (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA).obj T) :
    (reesClosedPerfectNativePushedCoefficientIso I G n iY g H p hp hR T hT).hom.hom
        (((reesClosedFrobeniusRingChartMap (ι := ι) I G p hp hR hA n).app T).hom x) =
      frobeniusDirectLimitMap p hp _ _
        (g.app (cechOpenIntersection (projectiveProjCechOpen G) T)).hom
        ((projectivePerfectNativeCechCoefficientIso G p hp hR T hT).hom.hom x) := by
  rw [reesClosedFrobeniusRingChartMap_app]
  obtain ⟨k, y, hy⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T)))
      p hp (projectiveHomogeneousChart_primeCast G p hR T)) x
  rw [hy]
  change frobeniusDirectLimitOf _ p hp _ k
      ((reesClosedNativeSectionRingIso I G n iY g H T hT).hom.hom
        (reesClosedHomogeneousChartProjection I G n T y)) =
    frobeniusDirectLimitOf _ p hp _ k _
  exact congrArg (frobeniusDirectLimitOf _ p hp _ k)
    (reesClosedNativeSectionRingIso_projection I G n iY g H T hT y)

/-- 固定した次数の各タプルで、閉厚化の制限と比較が可換。 -/
theorem reesClosedPerfectNativePushedCechIso_naturality_apply (q : ℕ)
    (a : (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).X q)
    (t : Fin (q + 1) → ι) :
    (((reesClosedPerfectNativePushedCechIso I G n iY g H p hp hR hA).hom.f q).hom
      (((reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA n).f q).hom a)) t =
    (((fullCechComplexMap (openCoverCechCoefficientMap
      (schemeStructurePerfectPullbackCoefficient g p hp
        (projectiveProjPresheaf_primeCast G p hR)
        (projectivePullbackPresheaf_primeCast G g p hR))
      (projectiveProjCechOpen (ι := ι) G))).f q).hom
      (((projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).hom.f q).hom a)) t := by
  rw [reesClosedPerfectNativePushedCechIso_apply]
  change _ = frobeniusDirectLimitMap p hp _ _
    (g.app (cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t))).hom
    ((((projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).hom.f q).hom a) t)
  rw [projectivePerfectNativeCechComplexIso_apply]
  exact reesClosedPerfectNativePushedCoefficientIso_projection I G n iY g H p hp hR hA
    (cechTupleSupport t) (cechTupleSupport_nonempty t) (a t)

/-- 押し出した切断の複体への比較は、実際の閉厚化の引き戻しに自然。 -/
theorem reesClosedPerfectNativePushedCechIso_naturality :
    reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA n ≫
      (reesClosedPerfectNativePushedCechIso I G n iY g H p hp hR hA).hom =
    (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).hom ≫
      fullCechComplexMap (openCoverCechCoefficientMap
        (schemeStructurePerfectPullbackCoefficient g p hp
          (projectiveProjPresheaf_primeCast G p hR)
          (projectivePullbackPresheaf_primeCast G g p hR))
        (projectiveProjCechOpen (ι := ι) G)) := by
  apply fullCechComplex_hom_ext
    (D := projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)
    (E := openCoverCechDiagram ((Opens.map g.base).op ⋙
      frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
      (projectiveProjCechOpen (ι := ι) G))
  intro q a t
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact reesClosedPerfectNativePushedCechIso_naturality_apply I G n iY g H p hp hR hA q a t

/-- 実際の Cartesian な閉厚化の逆像被覆への比較は、実際の構造層の引き戻しに自然。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の閉厚化に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedPerfectNativeCechIso_naturality :
    reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA n ≫
      (reesClosedPerfectNativeCechIso I G n iY g H p hp hR hA).hom =
    (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).hom ≫
      schemeStructurePerfectCechPullbackMap g p hp
        (projectiveProjPresheaf_primeCast G p hR)
        (projectivePullbackPresheaf_primeCast G g p hR)
        (projectiveProjCechOpen (ι := ι) G) := by
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  rw [← Category.assoc, reesClosedPerfectNativePushedCechIso_naturality,
    Category.assoc]

end SerrePositivity.AlgebraicGeometry
