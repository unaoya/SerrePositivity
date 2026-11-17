module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectCartesianSquareEdges
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechSquare

/-!
概要：F8 の実際の閉中心のスカラーを、既存の native な四角形へ渡す。
方針：構造射の可換性からスカラーの整合性を得て、同じ四角形の係数に代入する。
規約：全複体の完全性を仮定にせず、元の Cartesian な閉中心を保持する。
使われ方：F8 の既知の完全性を任意の有限アフィン被覆へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R)
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))))

include H in
/-- 元の Cartesian な構造射の四角から、同じ実際のスカラーの整合性を得る。 -/
theorem projectivePerfectCartesianScalarCompatibility :
    g.appTop.hom.comp (projectiveScalarToGlobalSections G) =
      (schemeScalarHom Y iY).comp (Ideal.Quotient.mk (I ^ 1)) := by
  have h := schemeScalarHom_naturality (Proj G) g
    (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) iY
    (Ideal.Quotient.mk (I ^ 1)) H.w
  rw [schemeScalarHom_scalarMorphism] at h
  exact h.symm

/-- 同じ射影的な閉中心のスカラーを、任意の被覆で既存の四角形に入れた値。 -/
def projectivePerfectCartesianScalarSquare
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    {κ : Type} [LinearOrder κ] (V : κ → (Proj G).Opens) : CechAugmentedSquare.{u} ℤ :=
  schemeStructurePerfectCechSquare g (Ideal.Quotient.mk (I ^ 1))
    (projectiveScalarToGlobalSections G) (schemeScalarHom Y iY)
    (projectivePerfectCartesianScalarCompatibility G I iY g H)
    p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
    (projectiveProjPresheaf_primeCast G p hR) (projectivePullbackPresheaf_primeCast G g p hR) V

end SerrePositivity.AlgebraicGeometry
