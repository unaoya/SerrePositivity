module

public import SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionComparison

/-!
概要：Cartesian な実際の閉厚化への係数比較が、環の同型であることを示す。
方針：同じ斉次局所化の射影の全射性と実際の引き戻しとの可換性から積を保つことを示す。
規約：線形同型を根拠なく環の同型と読み替えない。
使われ方：F8 の閉厚化の係数比較を Frobenius 順極限へ渡す。
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
local instance closedNativeSectionRingGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 斉次局所化の実際の商への射影は全射。 -/
theorem reesClosedHomogeneousChartProjection_surjective (T : Finset ι) :
    Function.Surjective (reesClosedHomogeneousChartProjection I G n T) := by
  intro y
  let eQ := projectiveHomogeneousChartLinearEquiv
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) T
  let eR := (Iso.app (reesClosedRingChartIso (ι := ι) I G n 0) T).toLinearEquiv
  let e := eR.trans eQ
  obtain ⟨z, hz⟩ := reesAdicProjectiveClosedChartProjection_surjective (ι := ι) I G n 0 T (e.symm y)
  refine ⟨projectiveHomogeneousChartLinearEquiv G T z, ?_⟩
  have hq := reesClosedHomogeneousChartProjection_compare I G n T z
  have hr := congrArg (fun η ↦ (η.app T).hom z) (reesClosedRingChartIso_projection (ι := ι) I G n 0)
  change eR (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0).app T).hom z) =
    ((reesClosedRingProjectionChartMap (ι := ι) I G n 0).app T).hom z at hr
  exact hq.symm.trans ((congrArg eQ hr).symm.trans
    ((congrArg e hz).trans (e.apply_symm_apply y)))

/-- 係数の線形同型は、実際の切断の環の同型を与える。 -/
def reesClosedNativeSectionRingIso (T : Finset ι) (hT : T.Nonempty) :
    CommRingCat.of (HomogeneousLocalization.Away
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
      (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ n).map (algebraMap R A))
        (projectiveLaurentDenominator R T))) ≅
      Γ(Y, g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen (ι := ι) G) T) :=
  RingEquiv.toCommRingCatIso {
    toEquiv := (reesClosedNativeSectionLinearEquiv I G n iY g H T hT).toEquiv
    map_add' := (reesClosedNativeSectionLinearEquiv I G n iY g H T hT).map_add
    map_mul' := by
      intro x y
      obtain ⟨a, rfl⟩ := reesClosedHomogeneousChartProjection_surjective I G n T x
      obtain ⟨b, rfl⟩ := reesClosedHomogeneousChartProjection_surjective I G n T y
      let e := reesClosedNativeSectionLinearEquiv I G n iY g H T hT
      let π := reesClosedHomogeneousChartProjection I G n T
      let k := (g.app (cechOpenIntersection (projectiveProjCechOpen G) T)).hom.comp
        (projectiveProjCechSectionRingIso G T hT).hom.hom
      change e (π a * π b) =
        @HMul.hMul Γ(Y, g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) T)
          Γ(Y, g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) T)
          Γ(Y, g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) T) inferInstance
          (e (π a)) (e (π b))
      calc
        _ = e (π (a * b)) := congrArg e (π.map_mul a b).symm
        _ = k (a * b) := reesClosedNativeSectionLinearEquiv_projection I G n iY g H T hT _
        _ = k a * k b := k.map_mul a b
        _ = _ := congrArg₂ (fun (x y : Γ(Y, g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) T)) ↦ x * y)
          (reesClosedNativeSectionLinearEquiv_projection I G n iY g H T hT a).symm
          (reesClosedNativeSectionLinearEquiv_projection I G n iY g H T hT b).symm }

/-- 実際の環の同型は、斉次局所化の射影を同じ構造層の引き戻しへ送る。 -/
theorem reesClosedNativeSectionRingIso_projection (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveHomogeneousChartDiagram G).obj T) :
    (reesClosedNativeSectionRingIso I G n iY g H T hT).hom.hom
        (reesClosedHomogeneousChartProjection I G n T x) =
      (g.app (cechOpenIntersection (projectiveProjCechOpen G) T)).hom
        ((projectiveProjCechSectionRingIso G T hT).hom.hom x) :=
  reesClosedNativeSectionLinearEquiv_projection I G n iY g H T hT x

end SerrePositivity.AlgebraicGeometry
