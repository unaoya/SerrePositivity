module

public import SerrePositivity.AlgebraicGeometry.ReesAdicNativeClosedCech
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullbackComposition

/-!
概要：Rees の閉厚化への射影と、実際の構造層の Čech の引き戻しを同じ射として照合する。
方針：係数の射影の一致を、逆像と交叉の比較に沿って移す。
規約：元の係数からの射と可換な canonical な比較を使う。
使われ方：実際の厚化間の I 進遷移と、比較同型との自然性。
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
local instance nativeClosedProjectionQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := S) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance nativeClosedProjectionQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := S) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n
local instance nativeClosedProjectionQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n
variable (n : ℕ) {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ n)))
variable (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))))

/-- Rees の射影と、実際の閉厚化への構造層の Čech の引き戻しとの一致。 -/
theorem reesAdicNativeClosedCechComplexIso_projection :
    fullCechComplexMap (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0) ≫
        (reesAdicNativeClosedCechComplexIso I G n iY g H).hom =
      (projectiveProjNativeNatCechComplexIso (ι := ι) G).hom ≫
        schemeStructureCechPullbackMap g (projectiveScalarToGlobalSections G)
          (g.appTop.hom.comp (projectiveScalarToGlobalSections G)) rfl
          (projectiveProjCechOpen (ι := ι) G) := by
  let e := schemeCechPreimageComplexIso g (projectiveProjPullbackCechPresheaf G g)
    (projectiveProjCechOpen (ι := ι) G)
  have hp := reesAdicNativeClosedPushedComplexIso_projection (ι := ι) I G n iY g H
  have hh := congrArg (fun f ↦ f ≫ e.hom) hp
  simpa only [reesAdicNativeClosedCechComplexIso, Iso.trans_hom,
    schemeStructureCechPullbackMap, schemeCechPullbackMap, Category.assoc] using hh

/-- 実際の引き戻しを恒等添字の細分として書いても、Rees の射影と一致する。 -/
theorem reesAdicNativeClosedCechComplexIso_projection_refined :
    fullCechComplexMap (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n 0) ≫
        (reesAdicNativeClosedCechComplexIso I G n iY g H).hom =
      (projectiveProjNativeNatCechComplexIso (ι := ι) G).hom ≫
        schemeStructureCechRefinedPullbackMap g (projectiveScalarToGlobalSections G)
          (g.appTop.hom.comp (projectiveScalarToGlobalSections G)) rfl
          (projectiveProjCechOpen (ι := ι) G)
          (fun i ↦ g ⁻¹ᵁ projectiveProjCechOpen (ι := ι) G i) id (fun _ ↦ le_rfl) := by
  rw [← schemeStructureCechPullbackMap_eq_refined]
  exact reesAdicNativeClosedCechComplexIso_projection I G n iY g H

end SerrePositivity.AlgebraicGeometry
