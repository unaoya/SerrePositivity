module

public import SerrePositivity.AlgebraicGeometry.ReesAdicClosedChartQuotient
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjClosedPullbackCoefficient
public import SerrePositivity.AlgebraicGeometry.CechQuotientComparison

/-!
概要：Rees の閉厚化の係数を、実際の閉厚化の非空交叉の切断と自然に比較する。
方針：元の次数零加群からの二つの全射が同じ核を持つことを使う。
規約：比較は実際の引き戻しと可換。空交叉では同型を仮定しない。
使われ方：閉厚化の Čech 複体・I 進遷移・形式関数を接続する。
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
local instance nativeClosedCoefficientQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := S) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance nativeClosedCoefficientQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := S) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n
local instance nativeClosedCoefficientQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n
variable (n : ℕ) {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n)))
variable (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- 実際の閉厚化の切断と Rees の商の、非空交叉での canonical な係数同型。 -/
def reesAdicNativeClosedCoefficientIso (T : Finset ι) (hT : T.Nonempty) :
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) 0).obj T ≅
      (openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
        (projectiveProjCechOpen (ι := ι) G)).obj T :=
  (cechQuotientComparison
    (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0).app T).hom)
    (projectiveProjClosedPullbackCoefficient G g T hT)
    (reesAdicProjectiveClosedChartProjection_surjective (ι := ι) I G n 0 T)
    (projectiveProjClosedPullbackCoefficient_surjective G g (I ^ n) iY H T hT)
    ((reesAdicProjectiveClosedChartProjection_ker (ι := ι) I G n 0 T).trans
      (projectiveProjClosedPullbackCoefficient_ker G g (I ^ n) iY H T hT).symm)).toModuleIso

/-- 係数同型は、元の係数からの射影を実際の引き戻しへ送る。 -/
theorem reesAdicNativeClosedCoefficientIso_projection_apply (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    (reesAdicNativeClosedCoefficientIso I G n iY g H T hT).hom.hom
      (((reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0).app T).hom x) =
        projectiveProjClosedPullbackCoefficient G g T hT x :=
  cechQuotientComparison_projection _ _ _ _ _ x

/-- 非空交叉の同型は、元の係数からの射影と実際の引き戻しを同じ射にする。 -/
theorem reesAdicNativeClosedCoefficientIso_projection (T : Finset ι) (hT : T.Nonempty) :
    (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0).app T ≫
        (reesAdicNativeClosedCoefficientIso I G n iY g H T hT).hom =
      ModuleCat.ofHom
        (X := (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T)
        (Y := (openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
          (projectiveProjCechOpen (ι := ι) G)).obj T)
        (projectiveProjClosedPullbackCoefficient G g T hT) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact reesAdicNativeClosedCoefficientIso_projection_apply I G n iY g H T hT

/-- 実際の閉厚化の切断への係数同型は、非空交叉の制限に自然。 -/
theorem reesAdicNativeClosedCoefficientIso_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) 0).map (homOfLE h) ≫
        (reesAdicNativeClosedCoefficientIso I G n iY g H U (hT.mono h)).hom =
      (reesAdicNativeClosedCoefficientIso I G n iY g H T hT).hom ≫
        (openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
          (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h) := by
  let D := projectiveNatGradedModuleChartDiagram (ι := ι) G 0
  let Q := projectiveNatGradedModuleChartDiagram (ι := ι)
    (reesAdicProjectiveQuotientPiece (ι := ι) I G n) 0
  let E := openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
    (projectiveProjCechOpen (ι := ι) G)
  let q : D ⟶ Q := reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := reesAdicProjectiveClosedChartProjection_surjective (ι := ι) I G n 0 T y
  have hq : (q.app U).hom ((D.map (homOfLE h)).hom x) =
      (Q.map (homOfLE h)).hom ((q.app T).hom x) :=
    congrArg (fun f : D.obj T ⟶ Q.obj U ↦ f.hom x) (q.naturality (homOfLE h))
  have hp := congrArg (fun f : D.obj T ⟶ E.obj U ↦ f.hom x)
    (projectiveProjClosedPullbackCoefficient_naturality G g hT h)
  change (reesAdicNativeClosedCoefficientIso I G n iY g H U (hT.mono h)).hom.hom
      ((Q.map (homOfLE h)).hom ((q.app T).hom x)) =
    (E.map (homOfLE h)).hom
      ((reesAdicNativeClosedCoefficientIso I G n iY g H T hT).hom.hom ((q.app T).hom x))
  calc
    _ = (reesAdicNativeClosedCoefficientIso I G n iY g H U (hT.mono h)).hom.hom
        ((q.app U).hom ((D.map (homOfLE h)).hom x)) := congrArg _ hq.symm
    _ = projectiveProjClosedPullbackCoefficient G g U (hT.mono h) ((D.map (homOfLE h)).hom x) :=
      reesAdicNativeClosedCoefficientIso_projection_apply I G n iY g H U (hT.mono h) _
    _ = (E.map (homOfLE h)).hom (projectiveProjClosedPullbackCoefficient G g T hT x) := hp
    _ = _ := congrArg (E.map (homOfLE h)).hom
      (reesAdicNativeClosedCoefficientIso_projection_apply I G n iY g H T hT x).symm

end SerrePositivity.AlgebraicGeometry
