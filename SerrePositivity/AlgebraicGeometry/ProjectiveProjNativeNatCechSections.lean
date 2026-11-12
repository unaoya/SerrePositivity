module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechFiniteness

/-!
概要：元の次数零加群の非空交叉と実際の構造層の切断を、係数ごとの同型として扱う。
方針：斉次局所化と標準開の二つの比較を合成する。
規約：空交叉の同型性は要求しない。
使われ方：閉厚化の商比較の共通の元の係数と、制限写像への自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 次数零加群で計算した標準開の非空交叉と、実際の切断の線形同型。 -/
def projectiveProjNativeNatCechSectionEquiv (T : Finset ι) (hT : T.Nonempty) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T ≃ₗ[R]
      (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
          (projectiveProjCechOpen (ι := ι) G)).obj T :=
  (projectiveHomogeneousChartLinearEquiv G T).trans (projectiveProjCechSectionLinearEquiv G T hT)

/-- 元の次数零加群から実際の切断への比較は、非空交叉の制限に自然。 -/
theorem projectiveProjNativeNatCechSectionEquiv_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map (homOfLE h) ≫
        (projectiveProjNativeNatCechSectionEquiv G U (hT.mono h)).toModuleIso.hom =
      (projectiveProjNativeNatCechSectionEquiv G T hT).toModuleIso.hom ≫
        (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
          ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
            (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h) := by
  change (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map (homOfLE h) ≫
      (projectiveHomogeneousChartDiagramIso (ι := ι) G).hom.app U ≫
        (projectiveProjCechSectionLinearEquiv G U (hT.mono h)).toModuleIso.hom =
    ((projectiveHomogeneousChartDiagramIso (ι := ι) G).hom.app T ≫
      (projectiveProjCechSectionLinearEquiv G T hT).toModuleIso.hom) ≫ _
  rw [← Category.assoc, (projectiveHomogeneousChartDiagramIso (ι := ι) G).hom.naturality,
    Category.assoc, projectiveProjCechSectionLinearEquiv_naturality G hT h]
  simp only [Category.assoc]

/-- 標準開の非空交叉は実際の Proj のアフィン開。 -/
theorem projectiveProjCechOpenIntersection_isAffineOpen (T : Finset ι) (hT : T.Nonempty) :
    IsAffineOpen (cechOpenIntersection (projectiveProjCechOpen (ι := ι) G) T) := by
  rw [← projectiveProjCechOpen_intersection]
  exact Proj.isAffineOpen_basicOpen G _ (projectivePolynomialDenominatorImage_mem G T)
    (Finset.card_pos.mpr hT)

end SerrePositivity.AlgebraicGeometry
