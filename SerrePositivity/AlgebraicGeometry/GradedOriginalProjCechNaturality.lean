module

public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechMaps

/-!
概要：次数零加群の Čech の射と、実際の構造層の引き戻しを同じ射として比較する。
方針：斉次分数の写像を標準開の切断へ移し、交叉との等式の輸送を自然性で処理する。
規約：原典のコホモロジーをここでは Čech 版で扱う。
使われ方：閉厚化と模型の遷移の実際の射に対する比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory HomogeneousIdeal Opposite
universe u v w
variable {R S A : Type u} {ι : Type} [CommRing R] [CommRing S] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable {σ τ : Type u}
variable [SetLike σ S] [AddSubgroupClass σ S] [SMulMemClass σ R S]
variable [SetLike τ A] [AddSubgroupClass τ A] [SMulMemClass τ R A]
variable (G : ℕ → σ) (H : ℕ → τ) [GradedRing G] [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : G →+*ᵍ H) (g : S →ₐ[MvPolynomial ι R] A) (hfg : ∀ x, f x = g x)
variable (hf : (irrelevant H) ≤ (irrelevant G).map f)

/-- 標準開上の分数の比較は、交叉の実際の切断への引き戻しに自然。 -/
theorem gradedOriginalProjNativeCechSection_map (T : Finset ι)
    (z : (projectiveNatGradedModuleChartDiagram (ι := ι) (gradedScalarComponents (R := R) G) 0).obj T) :
    ((Proj H).presheaf.map
      (eqToHom (gradedOriginalProjCechOpen_intersection (R := R) H T).symm).op).hom
      ((Proj.awayToSection H (algebraMap (MvPolynomial ι R) A
        (projectiveLaurentDenominator R T))).hom
        ((gradedScalarAwayIso (R := R) H _).hom.hom
          (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) H) T
          (((projectiveNatGradedModuleChartMap (gradedScalarComponents (R := R) G) (gradedScalarComponents (R := R) H) g.toLinearMap
            (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0).app T).hom z)))) =
    ((Proj.map f hf).appLE
      (cechOpenIntersection (gradedOriginalProjCechOpen (R := R) G) T)
      (cechOpenIntersection (gradedOriginalProjCechOpen (R := R) H) T)
      (by
        rw [← gradedOriginalProjCechOpen_intersection (R := R) G T,
          ← gradedOriginalProjCechOpen_intersection (R := R) H T, Proj.map_preimage_basicOpen,
          gradedOriginalScalarRingMap_denominator G H f g hfg T])).hom
      (((Proj G).presheaf.map
        (eqToHom (gradedOriginalProjCechOpen_intersection (R := R) G T).symm).op).hom
        ((Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
          (projectiveLaurentDenominator R T))).hom
          ((gradedScalarAwayIso (R := R) G _).hom.hom
            (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G) T z)))) := by
  rw [gradedOriginalChartLinearEquiv_map G H f g hfg T z]
  have hn := gradedOriginalProjRingMapSections_of_eq G H f hf
    (projectivePolynomialDenominatorImage_mem (gradedScalarComponents (R := R) G) T)
    (gradedOriginalScalarRingMap_denominator G H f g hfg T).symm
    (gradedOriginalScalarRingMap_powers G H f g hfg T)
  have hc :
      Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
          (projectiveLaurentDenominator R T)) ≫
        (Proj G).presheaf.map
          (eqToHom (gradedOriginalProjCechOpen_intersection (R := R) G T).symm).op ≫
        (Proj.map f hf).appLE
          (cechOpenIntersection (gradedOriginalProjCechOpen (R := R) G) T)
          (cechOpenIntersection (gradedOriginalProjCechOpen (R := R) H) T)
          (by rw [← gradedOriginalProjCechOpen_intersection (R := R) G T,
            ← gradedOriginalProjCechOpen_intersection (R := R) H T, Proj.map_preimage_basicOpen,
            gradedOriginalScalarRingMap_denominator G H f g hfg T]) =
      CommRingCat.ofHom (HomogeneousLocalization.map f
          (gradedOriginalScalarRingMap_powers G H f g hfg T)) ≫
        Proj.awayToSection H (algebraMap (MvPolynomial ι R) A
          (projectiveLaurentDenominator R T)) ≫
        (Proj H).presheaf.map
          (eqToHom (gradedOriginalProjCechOpen_intersection (R := R) H T).symm).op := by
    have hp := congrArg (fun k ↦ k ≫ (Proj H).presheaf.map
      (eqToHom (gradedOriginalProjCechOpen_intersection (R := R) H T).symm).op) hn
    simpa only [Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] using hp
  exact (congrArg (fun k ↦ k.hom ((gradedScalarAwayIso (R := R) G _).hom.hom
    (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G) T z))) hc).symm

/-- 次数零加群の Čech の射は、実際の構造層の Čech の引き戻しと一致する。
原典 Stacks 30.20.1 の射への自然性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem gradedOriginalProjNativeCechComplexIso_naturality :
    fullCechComplexMap (projectiveNatGradedModuleChartMap (gradedScalarComponents (R := R) G) (gradedScalarComponents (R := R) H) g.toLinearMap
      (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0) ≫
        (gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) H).hom =
      (gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) G).hom ≫
        gradedOriginalProjNativeCechMap G H f g hfg hf := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext t
  change (((gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) H).hom.f q).hom
      (((fullCechComplexMap (projectiveNatGradedModuleChartMap (gradedScalarComponents (R := R) G) (gradedScalarComponents (R := R) H) g.toLinearMap
        (fun n m hm ↦ by change g m ∈ H n; rw [← hfg]; exact f.2 hm) 0)).f q).hom a)) t =
    ((gradedOriginalProjNativeCechMap G H f g hfg hf).f q).hom
      (((gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) G).hom.f q).hom a) t
  rw [gradedOriginalProjNativeCechComplexIso_apply,
    gradedOriginalProjNativeCechMap_apply, gradedOriginalProjNativeCechComplexIso_apply]
  exact gradedOriginalProjNativeCechSection_map G H f g hfg hf (cechTupleSupport t) (a t)

end SerrePositivity.AlgebraicGeometry
