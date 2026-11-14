module

public import SerrePositivity.AlgebraicGeometry.ReesClosedNativeSectionEvaluation
public import SerrePositivity.AlgebraicGeometry.OpenCoverFrobeniusRefinement

/-!
概要：実際の閉厚化の非空交叉の環の比較を、環の図式の自然同型にする。
方針：非空有限集合の部分圏で同じ切断の環の同型と制限を使う。
規約：空交叉は図式から除き、元の全タプル複体では正の長さのタプルだけに適用する。
使われ方：環の図式に関する Frobenius の関手性を、閉厚化の比較へ適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

/-- 非空有限集合の部分圏から、全ての有限集合の圏への包含。 -/
def cechNonemptyIndexFunctor {ι : Type} [DecidableEq ι] :
    {T : Finset ι // T.Nonempty} ⥤ Finset ι where
  obj T := T.val
  map h := homOfLE (leOfHom h)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end SerrePositivity.AlgebraicGeometry

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
local instance closedNativeNonemptyDiagramGradedRing :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 非空交叉の環の係数図式と、実際の Cartesian な閉厚化の切断環の自然同型。 -/
def reesClosedNativeNonemptyRingIso :
    cechNonemptyIndexFunctor ⋙
      algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)) ≅
      cechNonemptyIndexFunctor ⋙
        openCoverCechRingDiagram ((Opens.map g.base).op ⋙ Y.presheaf)
          (projectiveProjCechOpen (ι := ι) G) :=
  NatIso.ofComponents (fun T ↦ reesClosedNativeSectionRingIso I G n iY g H T.val T.property) (by
    intro T U f
    change ((algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G))).map
          (homOfLE (leOfHom f))) ≫
        (reesClosedNativeSectionRingIso I G n iY g H U.val U.property).hom =
      (reesClosedNativeSectionRingIso I G n iY g H T.val T.property).hom ≫
        Y.presheaf.map ((Opens.map g.base).map
          (homOfLE (cechOpenIntersection_antitone (projectiveProjCechOpen G) (leOfHom f)))).op
    exact reesClosedNativeSectionRingIso_naturality_hom I G n iY g H T.property (leOfHom f))

end SerrePositivity.AlgebraicGeometry
