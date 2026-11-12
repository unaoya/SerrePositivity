module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeNatCechSections
public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphismSections
public import SerrePositivity.AlgebraicGeometry.SchemeAffineClosedBaseChangeSections
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechPullback

/-!
概要：次数零加群の係数から実際の閉厚化の切断への射を、同じ核で比較する。
方針：元の Proj の切断へ移し、構造層の実際の引き戻しを適用する。
規約：閉厚化は実際の Cartesian な正方形として指定し、flat を仮定しない。
使われ方：Rees の商の非空交叉の係数を、実際の閉厚化の切断に自然に移す。
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
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable {Y : Scheme.{u}} (g : Y ⟶ Proj G)

/-- 元の基底のスカラーを実際に引き戻して、構造層の係数前層を作る。 -/
abbrev projectiveProjPullbackCechPresheaf :=
  schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars
    (g.appTop.hom.comp (projectiveScalarToGlobalSections G))

/-- 非空交叉の次数零加群の係数から、実際に引き戻した切断への線形写像。 -/
def projectiveProjClosedPullbackCoefficient (T : Finset ι) (hT : T.Nonempty) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T →ₗ[R]
      (openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
        (projectiveProjCechOpen (ι := ι) G)).obj T :=
  (((openCoverCechCoefficientMap (schemeStructureCechPullbackCoefficient g
    (projectiveScalarToGlobalSections G)
    (g.appTop.hom.comp (projectiveScalarToGlobalSections G)) rfl)
    (projectiveProjCechOpen (ι := ι) G)).app T).hom).comp
      (projectiveProjNativeNatCechSectionEquiv G T hT).toLinearMap

/-- 係数の線形写像は、元の Proj の切断の実際の引き戻しそのもの。 -/
theorem projectiveProjClosedPullbackCoefficient_apply (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
    projectiveProjClosedPullbackCoefficient G g T hT x =
      (g.app (cechOpenIntersection (projectiveProjCechOpen G) T)).hom
        (projectiveProjNativeNatCechSectionEquiv G T hT x) := rfl

/-- 次数零加群から実際の切断への射は、非空交叉の制限に自然。 -/
theorem projectiveProjClosedPullbackCoefficient_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map (homOfLE h) ≫
        ModuleCat.ofHom (projectiveProjClosedPullbackCoefficient G g U (hT.mono h)) =
      ModuleCat.ofHom (projectiveProjClosedPullbackCoefficient G g T hT) ≫
        (openCoverCechDiagram ((Opens.map g.base).op ⋙ projectiveProjPullbackCechPresheaf G g)
          (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h) := by
  let η := openCoverCechCoefficientMap (schemeStructureCechPullbackCoefficient g
    (projectiveScalarToGlobalSections G)
    (g.appTop.hom.comp (projectiveScalarToGlobalSections G)) rfl)
    (projectiveProjCechOpen (ι := ι) G)
  change (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map (homOfLE h) ≫
      (projectiveProjNativeNatCechSectionEquiv G U (hT.mono h)).toModuleIso.hom ≫ η.app U =
    ((projectiveProjNativeNatCechSectionEquiv G T hT).toModuleIso.hom ≫ η.app T) ≫ _
  rw [← Category.assoc, projectiveProjNativeNatCechSectionEquiv_naturality G hT h,
    Category.assoc, η.naturality]
  simp only [Category.assoc]

variable (J : Ideal R) (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ J)))
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))

include H in
/-- 閉厚化への係数の写像は、実際の切断へ全射。 -/
theorem projectiveProjClosedPullbackCoefficient_surjective (T : Finset ι) (hT : T.Nonempty) :
    Function.Surjective (projectiveProjClosedPullbackCoefficient G g T hT) := by
  have hs : Function.Surjective
      (g.app (cechOpenIntersection (projectiveProjCechOpen G) T)).hom := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      schemeAffineClosedBaseChangeSections_surjective J
        (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)) iY g H
        (cechOpenIntersection (projectiveProjCechOpen G) T)
        (projectiveProjCechOpenIntersection_isAffineOpen G T hT)
  intro y
  obtain ⟨x, hx⟩ := hs y
  obtain ⟨z, hz⟩ := (projectiveProjNativeNatCechSectionEquiv G T hT).surjective x
  refine ⟨z, ?_⟩
  rw [projectiveProjClosedPullbackCoefficient_apply, hz]
  exact hx

include H in
/-- 閉厚化の実際の切断への係数の写像の核は、元の係数の J 倍。 -/
theorem projectiveProjClosedPullbackCoefficient_ker (T : Finset ι) (hT : T.Nonempty) :
    LinearMap.ker (projectiveProjClosedPullbackCoefficient G g T hT) =
      J • (⊤ : Submodule R ((projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T)) := by
  let U := cechOpenIntersection (projectiveProjCechOpen G) T
  let iX := schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G)
  let B := schemeAffineSectionAlgebra iX U
  let e := (projectiveProjNativeNatCechSectionEquiv G T hT).trans
    (schemeScalarMorphismSectionModuleEquiv (Proj G) (projectiveScalarToGlobalSections G) U)
  have hk := schemeAffineClosedBaseChangeSections_ker J iX iY g H U
    (projectiveProjCechOpenIntersection_isAffineOpen G T hT)
  have hmem (x : (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T) :
      projectiveProjClosedPullbackCoefficient G g T hT x = 0 ↔ e x ∈ J • (⊤ : Submodule R B) := by
    have hh := congrArg (fun K : Ideal Γ(Proj G, U) ↦ e x ∈ K) hk
    have hh' : (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom (e x) = 0 ↔
        e x ∈ J.map (algebraMap R B) := Iff.of_eq hh
    rw [projectiveProjClosedPullbackCoefficient_apply, Ideal.smul_top_eq_map]
    change (g.app U).hom (e x) = 0 ↔ e x ∈ J.map (algebraMap R B)
    simpa only [Scheme.Hom.appLE_eq_app] using hh'
  have himage : (J • (⊤ : Submodule R
      ((projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T))).map e.toLinearMap =
        J • (⊤ : Submodule R B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  ext x
  change projectiveProjClosedPullbackCoefficient G g T hT x = 0 ↔ _
  rw [hmem, ← himage, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

end SerrePositivity.AlgebraicGeometry
