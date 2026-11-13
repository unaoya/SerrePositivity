module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechFiniteness
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechMaps

/-!
概要：標準開の複体の比較と実際の引き戻しを、タプルごとの切断の式に戻す。
方針：非空交叉の環の同型と、引き戻しの appLE の表示を使う。
規約：次数零局所化の分子に元の係数の写像を適用することと照合する。
使われ方：五つの比較を、同じ実際の写像について閉じる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite HomogeneousIdeal
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 実際の構造層への複体の比較は、各タプルで非空交叉の切断の同型。 -/
theorem projectiveProjNativeNatCechComplexIso_apply (q : ℕ)
    (a : (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G 0)).X q)
    (t : Fin (q + 1) → ι) :
    (((projectiveProjNativeNatCechComplexIso (ι := ι) G).hom.f q).hom a) t =
      ((Proj G).presheaf.map
        (eqToHom (projectiveProjCechOpen_intersection G (cechTupleSupport t)).symm).op).hom
        ((Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
          (projectiveLaurentDenominator R (cechTupleSupport t)))).hom
          (projectiveHomogeneousChartLinearEquiv G (cechTupleSupport t) (a t))) := by
  change ((Proj G).presheaf.map
      (eqToHom (congrArg op (projectiveProjCechOpen_intersection G (cechTupleSupport t))))).hom
      ((Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
        (projectiveLaurentDenominator R (cechTupleSupport t)))).hom
          (projectiveHomogeneousChartLinearEquiv G (cechTupleSupport t) (a t))) = _
  congr 2

variable {A : Type u} [CommRing A] [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (H : ℕ → Submodule R A) [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : G →+*ᵍ H) (g : S →ₐ[MvPolynomial ι R] A) (hfg : ∀ x, f x = g x)
variable (hf : (irrelevant H) ≤ (irrelevant G).map f)

include hfg in
/-- 標準開の交叉は、実際の Proj の射での対応する交叉の逆像に含まれる。 -/
theorem projectiveProjNativeCech_intersection_le {k : ℕ} (t : Fin k → ι) :
    cechOpenIntersection (projectiveProjCechOpen H) (cechTupleSupport t) ≤
      Proj.map f hf ⁻¹ᵁ cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t) :=
  schemeCechRefinedPullbackIntersection_le (Proj.map f hf)
    (projectiveProjCechOpen G) (projectiveProjCechOpen H) id
    (fun i ↦ le_of_eq (projectiveProjNativeCech_preimageOpen G H f g hfg hf i).symm) t

/-- 実際の Proj の Čech の射は、タプルごとに構造層の appLE に等しい。 -/
theorem projectiveProjNativeCechMap_apply (q : ℕ)
    (a : (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
      ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
        (projectiveProjCechOpen (ι := ι) G))).X q) (t : Fin (q + 1) → ι) :
    ((projectiveProjNativeCechMap G H f g hfg hf).f q).hom a t =
      ((Proj.map f hf).appLE
        (cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t))
        (cechOpenIntersection (projectiveProjCechOpen H) (cechTupleSupport t))
        (projectiveProjNativeCech_intersection_le G H f g hfg hf t)).hom (a t) :=
  schemeStructureCechRefinedPullbackMap_apply (Proj.map f hf)
    (projectiveScalarToGlobalSections G) (projectiveScalarToGlobalSections H)
    (projectiveScalarToGlobalSections_naturality G H f g hfg hf)
    (projectiveProjCechOpen G) (projectiveProjCechOpen H) id
    (fun i ↦ le_of_eq (projectiveProjNativeCech_preimageOpen G H f g hfg hf i).symm) q a t

end SerrePositivity.AlgebraicGeometry
