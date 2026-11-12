module

public import SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedCoefficient
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechHomology

/-!
概要：Rees の商の計算を、実際の閉厚化の構造層の Čech 複体と H へ移す。
方針：非空交叉の自然な同型を複体にまとめ、逆像と交叉の比較を合成する。
規約：非 flat な H とテンソル積の交換は使わない。
使われ方：実際の閉厚化の I 進系と、既存の Rees の形式関数への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (I : Ideal R) (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance nativeClosedCechQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := S) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance nativeClosedCechQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := S) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n
local instance nativeClosedCechQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n
variable (n : ℕ) {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n)))
variable (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- Rees の商の Čech 複体と、実際の切断を押し出した係数の複体との同型。 -/
def reesAdicNativeClosedPushedComplexIso :
    fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) 0) ≅
      fullCechComplex (openCoverCechDiagram
        ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
        (projectiveProjCechOpen (ι := ι) G)) :=
  fullCechNonemptyComplexIso
    (fun T hT ↦ reesAdicNativeClosedCoefficientIso I G n iY g H T hT)
    (fun hT h ↦ reesAdicNativeClosedCoefficientIso_naturality I G n iY g H hT h)

/-- Rees の商の Čech 複体と、実際の閉厚化の逆像被覆の Čech 複体との同型。 -/
def reesAdicNativeClosedCechComplexIso :
    fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) 0) ≅
      fullCechComplex (openCoverCechDiagram (projectiveProjPullbackCechPresheaf G g)
        (fun i ↦ g ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i)) :=
  reesAdicNativeClosedPushedComplexIso I G n iY g H ≪≫
    schemeCechPreimageComplexIso g (projectiveProjPullbackCechPresheaf G g)
      (projectiveProjCechOpen (ι := ι) G)

/-- Rees の商の H と、実際の閉厚化の構造層の Čech H の比較。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の係数の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicNativeClosedCechHomologyIso (q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I G n 0 q ≅
      (fullCechComplex (openCoverCechDiagram (projectiveProjPullbackCechPresheaf G g)
        (fun i ↦ g ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i))).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q).mapIso
    (reesAdicNativeClosedCechComplexIso I G n iY g H)

/-- 元の係数からの Rees の射影は、実際の切断を引き戻す Čech の射と一致する。 -/
theorem reesAdicNativeClosedPushedComplexIso_projection :
    fullCechComplexMap (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0) ≫
        (reesAdicNativeClosedPushedComplexIso I G n iY g H).hom =
      (projectiveProjNativeNatCechComplexIso (ι := ι) G).hom ≫
        fullCechComplexMap (openCoverCechCoefficientMap (schemeStructureCechPullbackCoefficient g
          (projectiveScalarToGlobalSections G)
          (g.appTop.hom.comp (projectiveScalarToGlobalSections G)) rfl)
          (projectiveProjCechOpen (ι := ι) G)) := by
  let D := projectiveNatGradedModuleChartDiagram (ι := ι) G 0
  let E := openCoverCechDiagram
    ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
    (projectiveProjCechOpen (ι := ι) G)
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext t
  exact congrArg (fun f : D.obj (cechTupleSupport t) ⟶ E.obj (cechTupleSupport t) ↦
    f.hom (a t))
    (reesAdicNativeClosedCoefficientIso_projection I G n iY g H
      (cechTupleSupport t) (cechTupleSupport_nonempty t))

end SerrePositivity.AlgebraicGeometry
