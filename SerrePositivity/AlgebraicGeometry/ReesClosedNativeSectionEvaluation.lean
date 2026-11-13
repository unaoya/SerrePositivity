module

public import SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionNaturality

/-!
概要：閉厚化の環の同型の値を、検証済みの係数の線形同型の値として表示する。
方針：環同型の構成の関数部分を一度だけ取り出す。
規約：環の同型の積の保存の証明を利用側で展開しない。
使われ方：非空交叉の環の自然同型を計算量上限内で組み立てる。
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
local instance closedNativeSectionEvaluationGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 環の同型の関数部分は、2e からの同じ係数の線形同型。 -/
theorem reesClosedNativeSectionRingIso_hom_apply (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveHomogeneousChartDiagram
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)).obj T) :
    (reesClosedNativeSectionRingIso I G n iY g H T hT).hom.hom x =
      reesClosedNativeSectionLinearEquiv I G n iY g H T hT x := rfl

/-- 閉厚化の環の比較と制限の可換性を、環の圏の等式として使う。 -/
theorem reesClosedNativeSectionRingIso_naturality_hom {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G))).map (homOfLE h) ≫
        (reesClosedNativeSectionRingIso I G n iY g H U (hT.mono h)).hom =
      (reesClosedNativeSectionRingIso I G n iY g H T hT).hom ≫
        Y.presheaf.map ((Opens.map g.base).map
          (homOfLE (cechOpenIntersection_antitone (projectiveProjCechOpen G) h))).op := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change HomogeneousLocalization.Away
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
    (algebraMap (MvPolynomial ι R) (A ⧸ (I ^ n).map (algebraMap R A))
      (projectiveLaurentDenominator R T)) at x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  have hn := reesClosedNativeSectionRingIso_naturality I G n iY g H hT h x
  dsimp only [algebraCechRingDiagram, projectiveHomogeneousChartAlgebraDiagram,
    Functor.comp_obj, Functor.comp_map, CommAlgCat.hasForgetToCommRingCat,
    closedNativeSectionEvaluationGradedRing, reesClosedNativeSectionRingIso,
    RingEquiv.toCommRingCatIso] at *
  convert hn using 1

end SerrePositivity.AlgebraicGeometry
