module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectNativeCechMaps
public import SerrePositivity.AlgebraicGeometry.FullCechComplexHomExt

/-!
概要：F8 の固定した複体と実際の構造層の比較を、次数を保つ環の射に自然にする。
方針：各タプルを Frobenius の有限段に戻し、2e の実際の appLE との等式を使う。
規約：native な引き戻しを比較で移した射として定義せず、実際の Proj の射と照合する。
使われ方：閉厚化・商表示と全複体の比較。
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
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0) (hA : (p : A) = 0)

/-- 非空交叉の係数の比較は、実際の環の射と可換。 -/
theorem projectivePerfectNativeCechCoefficientIso_map
    (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hS).obj T) :
    (projectivePerfectNativeCechCoefficientIso H p hp hR T hT).hom.hom
        (((projectivePerfectChartMap G H f g hfg p hp hR hS hA).app T).hom x) =
      frobeniusDirectLimitMap p hp _ _
        ((Proj.map f hf).appLE
          (cechOpenIntersection (projectiveProjCechOpen G) T)
          (cechOpenIntersection (projectiveProjCechOpen H) T)
          (by rw [← projectiveProjCechOpen_intersection G T,
            ← projectiveProjCechOpen_intersection H T, Proj.map_preimage_basicOpen,
            projectiveHomogeneousRingChartMap_denominator G H f g hfg T])).hom
        ((projectivePerfectNativeCechCoefficientIso G p hp hR T hT).hom.hom x) := by
  change frobeniusDirectLimitMap p hp _ _ (projectiveProjCechSectionRingIso H T hT).hom.hom
      (frobeniusDirectLimitMap p hp _ _
        (HomogeneousLocalization.map f (projectiveHomogeneousRingChartMap_powers G H f g hfg T)) x) =
    frobeniusDirectLimitMap p hp _ _ _
      (frobeniusDirectLimitMap p hp _ _ (projectiveProjCechSectionRingIso G T hT).hom.hom x)
  obtain ⟨n, y, hy⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap (HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)))
        p hp (projectiveHomogeneousChart_primeCast G p hR T)) x
  rw [hy]
  change frobeniusDirectLimitOf _ p hp _ n
      ((projectiveProjCechSectionRingIso H T hT).hom.hom
        (HomogeneousLocalization.map f (projectiveHomogeneousRingChartMap_powers G H f g hfg T) y)) =
    frobeniusDirectLimitOf _ p hp _ n _
  exact congrArg (frobeniusDirectLimitOf _ p hp _ n)
    (projectiveProjCechSectionRingIso_map G H f g hfg hf T hT y)

/-- 複体の比較の自然性を、固定した次数の各タプルで表す。 -/
theorem projectivePerfectNativeCechComplexIso_naturality_apply (q : ℕ)
    (a : (fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hS)).X q)
    (t : Fin (q + 1) → ι) :
    (((projectivePerfectNativeCechComplexIso (ι := ι) H p hp hR hA).hom.f q).hom
      (((fullCechComplexMap (projectivePerfectChartMap G H f g hfg p hp hR hS hA)).f q).hom a)) t =
    ((projectivePerfectNativeCechMap G H f g hfg hf p hp hR).f q).hom
      (((projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hS).hom.f q).hom a) t := by
  rw [projectivePerfectNativeCechComplexIso_apply H p hp hR hA,
    projectivePerfectNativeCechMap_apply G H f g hfg hf p hp hR,
    projectivePerfectNativeCechComplexIso_apply G p hp hR hS]
  exact projectivePerfectNativeCechCoefficientIso_map G H f g hfg hf p hp hR hS hA
    (cechTupleSupport t) (cechTupleSupport_nonempty t) (a t)

/-- 固定した斉次局所化の複体と native な構造層の比較は、実際の環の射に自然。
BST13 Lemma 3.9 と Stacks 30.2.6 の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfectNativeCechComplexIso_naturality :
    fullCechComplexMap (projectivePerfectChartMap G H f g hfg p hp hR hS hA) ≫
        (projectivePerfectNativeCechComplexIso (ι := ι) H p hp hR hA).hom =
      (projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hS).hom ≫
        projectivePerfectNativeCechMap G H f g hfg hf p hp hR := by
  apply fullCechComplex_hom_ext
    (D := projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hS)
    (E := openCoverCechDiagram
      (frobeniusRingDiagram (Proj H).presheaf p hp (projectiveProjPresheaf_primeCast H p hR))
        (projectiveProjCechOpen (ι := ι) H))
  intro q a t
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact projectivePerfectNativeCechComplexIso_naturality_apply G H f g hfg hf p hp hR hS hA q a t

end SerrePositivity.AlgebraicGeometry
