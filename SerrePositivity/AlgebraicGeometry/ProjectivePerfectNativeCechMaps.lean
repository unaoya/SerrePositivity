module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechComparison
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousRingDiagramMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechNaturality
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechRefinedPullback

/-!
概要：次数付き環の写像について、F8 の Frobenius 係数の射と native な Proj の引き戻しを定義する。
方針：斉次局所化の環の写像と、実際の Proj の appLE の写像を別々に作って照合する。
規約：引き戻しを斉次局所化の比較から定義せず、実際のスキームの射を使う。
使われ方：閉厚化・商表示の射の自然性を F8 の全複体へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory HomogeneousLocalization HomogeneousIdeal TopologicalSpace
  _root_.AlgebraicGeometry
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
variable (hf : irrelevant H ≤ (irrelevant G).map f)

/-- 標準開交叉での環の同型は、実際の Proj の appLE に自然。 -/
theorem projectiveProjCechSectionRingIso_map (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveHomogeneousChartDiagram G).obj T) :
    (projectiveProjCechSectionRingIso H T hT).hom.hom
        (HomogeneousLocalization.map f (projectiveHomogeneousRingChartMap_powers G H f g hfg T) x) =
      ((Proj.map f hf).appLE
        (cechOpenIntersection (projectiveProjCechOpen G) T)
        (cechOpenIntersection (projectiveProjCechOpen H) T)
        (by rw [← projectiveProjCechOpen_intersection G T,
          ← projectiveProjCechOpen_intersection H T, Proj.map_preimage_basicOpen,
          projectiveHomogeneousRingChartMap_denominator G H f g hfg T])).hom
        ((projectiveProjCechSectionRingIso G T hT).hom.hom x) := by
  have h := projectiveProjNativeCechSection_map G H f g hfg hf T
    ((projectiveHomogeneousChartLinearEquiv G T).symm x)
  rw [projectiveHomogeneousChartLinearEquiv_map G H f g hfg,
    LinearEquiv.apply_symm_apply] at h
  exact h

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0) (hA : (p : A) = 0)

/-- 実際の斉次局所化の環の写像から作る、F8 の固定した係数図式の射。 -/
def projectivePerfectChartMap :
    projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hS ⟶
      projectiveFrobeniusRingChartDiagram (ι := ι) H p hp hR hA :=
  (projectiveFrobeniusRingChartDiagram_isoCanonical G p hp hR hS).hom ≫
    frobeniusRingDiagramMap p hp (fun T ↦ projectiveHomogeneousChart_primeCast G p hR T)
      (hE := fun T ↦ projectiveHomogeneousChart_primeCast H p hR T)
      (projectiveHomogeneousRingDiagramMap G H f g hfg) ≫
    (projectiveFrobeniusRingChartDiagram_isoCanonical H p hp hR hA).inv

/-- Proj の実際のスキームの射から作る、Frobenius 後の標準開の複体の引き戻し。 -/
def projectivePerfectNativeCechMap :
    fullCechComplex (openCoverCechDiagram
      (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
        (projectiveProjCechOpen (ι := ι) G)) ⟶
      fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram (Proj H).presheaf p hp (projectiveProjPresheaf_primeCast H p hR))
          (projectiveProjCechOpen (ι := ι) H)) :=
  schemeStructurePerfectCechRefinedPullbackMap (Proj.map f hf) p hp
    (projectiveProjPresheaf_primeCast G p hR) (projectiveProjPresheaf_primeCast H p hR)
    (projectiveProjCechOpen (ι := ι) G) (projectiveProjCechOpen (ι := ι) H) id
    (fun i ↦ le_of_eq (projectiveProjNativeCech_preimageOpen G H f g hfg hf i).symm)

/-- native な写像の各タプルは、実際の Proj の appLE の環の射の順極限。 -/
theorem projectivePerfectNativeCechMap_apply (q : ℕ)
    (a : (fullCechComplex (openCoverCechDiagram
      (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
        (projectiveProjCechOpen (ι := ι) G))).X q) (t : Fin (q + 1) → ι) :
    ((projectivePerfectNativeCechMap G H f g hfg hf p hp hR).f q).hom a t =
      frobeniusDirectLimitMap p hp _ _
        ((Proj.map f hf).appLE
          (cechOpenIntersection (projectiveProjCechOpen G) (cechTupleSupport t))
          (cechOpenIntersection (projectiveProjCechOpen H) (cechTupleSupport t))
          (projectiveProjNativeCech_intersection_le G H f g hfg hf t)).hom (a t) :=
  schemeStructurePerfectCechRefinedPullbackMap_apply (Proj.map f hf) p hp
    (projectiveProjPresheaf_primeCast G p hR) (projectiveProjPresheaf_primeCast H p hR)
    (projectiveProjCechOpen G) (projectiveProjCechOpen H) id
    (fun i ↦ le_of_eq (projectiveProjNativeCech_preimageOpen G H f g hfg hf i).symm) q a t

end SerrePositivity.AlgebraicGeometry
