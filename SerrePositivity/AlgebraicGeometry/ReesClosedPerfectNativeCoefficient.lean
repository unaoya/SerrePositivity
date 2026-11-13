module

public import SerrePositivity.AlgebraicGeometry.ReesClosedNativeNonemptyDiagram
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIsoNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechPullback

/-!
概要：実際の Cartesian な閉厚化への環の係数比較を、Frobenius 後の複体へ渡す。
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
local instance closedPerfectNativeCoefficientGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

include hR g in
/-- 元の基底の p の零化は、Proj に写るスキームの全ての切断環で成り立つ。 -/
theorem projectivePullbackPresheaf_primeCast (O : Y.Opensᵒᵖ) :
    (p : Y.presheaf.obj O) = 0 := by
  let f := (Y.presheaf.map (homOfLE (show O.unop ≤ ⊤ from le_top)).op).hom.comp
    (g.appTop.hom.comp (projectiveScalarToGlobalSections G))
  simpa only [map_natCast, map_zero] using congrArg f hR

/-- 非空交叉の環の自然同型に Frobenius の関手を適用した自然同型。 -/
def reesClosedPerfectNativeNonemptyIso :
    cechNonemptyIndexFunctor ⋙ projectiveHomogeneousPerfectChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR ≅
      cechNonemptyIndexFunctor ⋙ openCoverCechDiagram ((Opens.map g.base).op ⋙
        frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
        (projectiveProjCechOpen (ι := ι) G) :=
  frobeniusRingDiagramIso p hp
    (fun T ↦ projectiveHomogeneousChart_primeCast
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hR T.val)
    (hE := fun T ↦ projectivePullbackPresheaf_primeCast G g p hR
      (Opposite.op (g ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) T.val)))
    (reesClosedNativeNonemptyRingIso I G n iY g H)

/-- 非空交叉の環の同型が誘導する、実際の Frobenius 順極限の係数の同型。 -/
def reesClosedPerfectNativePushedCoefficientIso (T : Finset ι) (hT : T.Nonempty) :
    (projectiveHomogeneousPerfectChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR).obj T ≅
      (openCoverCechDiagram ((Opens.map g.base).op ⋙
        frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
        (projectiveProjCechOpen (ι := ι) G)).obj T :=
  Iso.app (reesClosedPerfectNativeNonemptyIso I G n iY g H p hp hR) ⟨T, hT⟩

/-- 実際の閉厚化の Frobenius 係数の比較は、非空交叉の制限に自然。 -/
theorem reesClosedPerfectNativePushedCoefficientIso_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveHomogeneousPerfectChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR).map (homOfLE h) ≫
      (reesClosedPerfectNativePushedCoefficientIso I G n iY g H p hp hR U (hT.mono h)).hom =
    (reesClosedPerfectNativePushedCoefficientIso I G n iY g H p hp hR T hT).hom ≫
      (openCoverCechDiagram ((Opens.map g.base).op ⋙
        frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
        (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h) := by
  exact (reesClosedPerfectNativeNonemptyIso I G n iY g H p hp hR).hom.naturality
    (homOfLE (show (⟨T, hT⟩ : {T : Finset ι // T.Nonempty}) ≤ ⟨U, hT.mono h⟩ from h))

/-- 固定した閉厚化の複体と、実際の閉厚化の切断を押し出した係数の複体の同型。 -/
def reesClosedPerfectNativePushedCechIso :
    fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))) ≅
      fullCechComplex (openCoverCechDiagram ((Opens.map g.base).op ⋙
        frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
        (projectiveProjCechOpen (ι := ι) G)) :=
  fullCechComplexFunctor.mapIso (projectiveFrobeniusRingChartDiagram_isoCanonical (ι := ι)
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))) ≪≫
      fullCechNonemptyComplexIso (reesClosedPerfectNativePushedCoefficientIso I G n iY g H p hp hR)
        (fun hT h ↦ reesClosedPerfectNativePushedCoefficientIso_naturality I G n iY g H p hp hR hT h)

/-- 押し出した切断の複体への比較は、各タプルで同じ係数の同型を使う。 -/
theorem reesClosedPerfectNativePushedCechIso_apply (q : ℕ)
    (a : (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))))).X q)
    (t : Fin (q + 1) → ι) :
    (((reesClosedPerfectNativePushedCechIso I G n iY g H p hp hR hA).hom.f q).hom a) t =
      (reesClosedPerfectNativePushedCoefficientIso I G n iY g H p hp hR
        (cechTupleSupport t) (cechTupleSupport_nonempty t)).hom.hom (a t) := rfl

/-- F8 の固定した閉厚化の複体と、実際の Cartesian な閉厚化の逆像被覆の複体の同型。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の閉厚化に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedPerfectNativeCechIso :
    fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A)))) ≅
      fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
        (fun i ↦ g ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i)) :=
  reesClosedPerfectNativePushedCechIso I G n iY g H p hp hR hA ≪≫
    schemeCechPreimageComplexIso g
      (frobeniusRingDiagram Y.presheaf p hp (projectivePullbackPresheaf_primeCast G g p hR))
      (projectiveProjCechOpen (ι := ι) G)

end SerrePositivity.AlgebraicGeometry
