module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartAlgebra
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousRingChartMap
public import SerrePositivity.AlgebraicGeometry.CechAlgebraIntH0Naturality

/-!
概要：次数を保つ環の写像を、斉次局所化の実際の環の係数図式の射にまとめる。
方針：2e の次数零加群の自然変換を斉次局所化へ移し、既存の環の写像との等式を使う。
規約：多項式環の作用と次数を保つことを明示する。
使われ方：F8 の native な比較を、閉厚化・模型の係数写像に自然にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory HomogeneousLocalization
universe u
variable {R S A : Type u} {ι : Type} [CommRing R] [CommRing S] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R S) (H : ℕ → Submodule R A) [GradedRing G] [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : G →+*ᵍ H) (g : S →ₐ[MvPolynomial ι R] A) (hfg : ∀ x, f x = g x)

/-- 同じ次数零加群の射を、斉次局所化の線形な係数図式へ移す。 -/
def projectiveHomogeneousModuleDiagramMap :
    projectiveHomogeneousChartDiagram (ι := ι) G ⟶ projectiveHomogeneousChartDiagram (ι := ι) H :=
  (projectiveHomogeneousChartDiagramIso G).inv ≫
    projectiveNatGradedModuleChartMap G H g.toLinearMap
      (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0 ≫
    (projectiveHomogeneousChartDiagramIso H).hom

/-- 移した線形写像は、実際の斉次局所化の環の写像に等しい。 -/
theorem projectiveHomogeneousModuleDiagramMap_apply (T : Finset ι)
    (x : (projectiveHomogeneousChartDiagram G).obj T) :
    ((projectiveHomogeneousModuleDiagramMap G H f g hfg).app T).hom x =
      HomogeneousLocalization.map f (projectiveHomogeneousRingChartMap_powers G H f g hfg T) x := by
  change projectiveHomogeneousChartLinearEquiv H T
    (((projectiveNatGradedModuleChartMap G H g.toLinearMap
      (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0).app T).hom
        ((projectiveHomogeneousChartLinearEquiv G T).symm x)) = _
  rw [projectiveHomogeneousChartLinearEquiv_map G H f g hfg, LinearEquiv.apply_symm_apply]

/-- 実際の環の係数図式の射。 -/
def projectiveHomogeneousRingDiagramMap :
    algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) ⟶
      algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι) H) where
  app T := CommRingCat.ofHom
    (HomogeneousLocalization.map f (projectiveHomogeneousRingChartMap_powers G H f g hfg T))
  naturality {T U} h := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change HomogeneousLocalization.map f
        (projectiveHomogeneousRingChartMap_powers G H f g hfg U)
        (((projectiveHomogeneousChartDiagram G).map h).hom x) =
      ((projectiveHomogeneousChartDiagram H).map h).hom
        (HomogeneousLocalization.map f
          (projectiveHomogeneousRingChartMap_powers G H f g hfg T) x)
    rw [← projectiveHomogeneousModuleDiagramMap_apply G H f g hfg,
      ← projectiveHomogeneousModuleDiagramMap_apply G H f g hfg]
    exact congrArg (fun m ↦ m.hom x)
      ((projectiveHomogeneousModuleDiagramMap G H f g hfg).naturality h)

end SerrePositivity.AlgebraicGeometry
