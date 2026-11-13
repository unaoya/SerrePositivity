module

public import SerrePositivity.AlgebraicGeometry.FrobeniusRingDiagram
public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusRingChartDiagram
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartAlgebra

/-!
概要：F8 の実際の環の係数図式を、環の図式の Frobenius 順極限の自然な構成と同定する。
方針：対象ごとは恒等、制限は既存の実際の環準同型との照合を使う。
規約：F8 で用いた係数図式の写像を置き換えず、等しいことを示す。
使われ方：2e の環の切断の射に沿う Frobenius と全複体の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 各標準開の環の図式から直接作る、自然な Frobenius 順極限の係数図式。 -/
def projectiveHomogeneousPerfectChartDiagram : Finset ι ⥤ ModuleCat.{u} ℤ :=
  frobeniusRingDiagram
    (algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)) p hp
    (fun T ↦ projectiveHomogeneousChart_primeCast G p hR T)

/-- F8 の環の係数図式は、環の図式から直接作るものと制限も含めて一致する。 -/
def projectiveFrobeniusRingChartDiagram_isoCanonical :
    projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA ≅
      projectiveHomogeneousPerfectChartDiagram (ι := ι) G p hp hR :=
  NatIso.ofComponents (fun T ↦ Iso.refl _) (by
    intro T U f
    let h : T ⊆ U := leOfHom f
    have hf : f = homOfLE h := Subsingleton.elim _ _
    rw [hf]
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [projectiveFrobeniusRingChartDiagram_map]
    have hr : ((algebraCechRingDiagram
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)).map
          (homOfLE h)).hom =
        projectiveHomogeneousChartRestrictionRingHom G h := by
      ext x
      exact projectiveHomogeneousChartDiagram_map G h x
    change ModuleCat.ofHom (frobeniusDirectLimitMap p hp
      (projectiveHomogeneousChart_primeCast G p hR T)
      (projectiveHomogeneousChart_primeCast G p hR U)
      (projectiveHomogeneousChartRestrictionRingHom G h)).toAddMonoidHom.toIntLinearMap =
      ModuleCat.ofHom (frobeniusDirectLimitMap p hp
        (projectiveHomogeneousChart_primeCast G p hR T)
        (projectiveHomogeneousChart_primeCast G p hR U)
        ((algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G)).map
          (homOfLE h)).hom).toAddMonoidHom.toIntLinearMap
    rw [hr])

end SerrePositivity.AlgebraicGeometry
