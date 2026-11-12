module

public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjCech
public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjScalarNaturality
public import SerrePositivity.AlgebraicGeometry.GradedOriginalScalarRingMap
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechRefinedPullback

/-!
概要：基底ごとの元の grading の Proj の射を、共通基底上の Čech の射として扱う。
方針：元の構造層の引き戻しを使い、各タプルの appLE の式を明示する。
規約：各段の Proj 自体を carrier を変えた別の Proj と同一視しない。
使われ方：動く基底の標準開と filtered colimit の実際の遷移の比較。
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

include hfg in
/-- 元の grading の Proj の射は、同じ変数の標準開を引き戻す。 -/
theorem gradedOriginalProjCech_preimageOpen (i : ι) :
    Proj.map f hf ⁻¹ᵁ gradedOriginalProjCechOpen (R := R) G i =
      gradedOriginalProjCechOpen (R := R) H i := by
  change Proj.map f hf ⁻¹ᵁ Proj.basicOpen G _ = Proj.basicOpen H _
  rw [Proj.map_preimage_basicOpen, hfg, g.commutes]

/-- 元の二つの grading の間の、実際の構造層の Čech の引き戻し。 -/
def gradedOriginalProjNativeCechMap :=
  schemeStructureCechRefinedPullbackMap (Proj.map f hf)
    (gradedOriginalScalarToGlobalSections (R := R) G)
    (gradedOriginalScalarToGlobalSections (R := R) H)
    (gradedOriginalScalarToGlobalSections_naturality G H f g hfg hf)
    (gradedOriginalProjCechOpen (R := R) (ι := ι) G)
    (gradedOriginalProjCechOpen (R := R) (ι := ι) H) id
    (fun i ↦ le_of_eq (gradedOriginalProjCech_preimageOpen G H f g hfg hf i).symm)

include hfg in
/-- 元の grading の標準開の交叉を引き戻す包含。 -/
theorem gradedOriginalProjCech_intersection_le {k : ℕ} (t : Fin k → ι) :
    cechOpenIntersection (gradedOriginalProjCechOpen (R := R) H) (cechTupleSupport t) ≤
      Proj.map f hf ⁻¹ᵁ cechOpenIntersection
        (gradedOriginalProjCechOpen (R := R) G) (cechTupleSupport t) :=
  schemeCechRefinedPullbackIntersection_le (Proj.map f hf)
    (gradedOriginalProjCechOpen (R := R) G) (gradedOriginalProjCechOpen (R := R) H) id
    (fun i ↦ le_of_eq (gradedOriginalProjCech_preimageOpen G H f g hfg hf i).symm) t

/-- 共通基底上での元の Proj の Čech の射は、実際の appLE の引き戻し。 -/
theorem gradedOriginalProjNativeCechMap_apply (q : ℕ)
    (a : (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
      ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections (R := R) G))
        (gradedOriginalProjCechOpen (R := R) (ι := ι) G))).X q)
    (t : Fin (q + 1) → ι) :
    ((gradedOriginalProjNativeCechMap G H f g hfg hf).f q).hom a t =
      ((Proj.map f hf).appLE
        (cechOpenIntersection (gradedOriginalProjCechOpen (R := R) G) (cechTupleSupport t))
        (cechOpenIntersection (gradedOriginalProjCechOpen (R := R) H) (cechTupleSupport t))
        (gradedOriginalProjCech_intersection_le G H f g hfg hf t)).hom (a t) :=
  schemeStructureCechRefinedPullbackMap_apply (Proj.map f hf)
    (gradedOriginalScalarToGlobalSections (R := R) G)
    (gradedOriginalScalarToGlobalSections (R := R) H)
    (gradedOriginalScalarToGlobalSections_naturality G H f g hfg hf)
    (gradedOriginalProjCechOpen (R := R) G) (gradedOriginalProjCechOpen (R := R) H) id
    (fun i ↦ le_of_eq (gradedOriginalProjCech_preimageOpen G H f g hfg hf i).symm) q a t

/-- 共通基底の加群の複体と元の Proj の切断の比較を、タプルごとに計算する。 -/
theorem gradedOriginalProjNativeCechComplexIso_apply (q : ℕ)
    (a : (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (gradedScalarComponents (R := R) G) 0)).X q) (t : Fin (q + 1) → ι) :
    (((gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) G).hom.f q).hom a) t =
      ((Proj G).presheaf.map
        (eqToHom (gradedOriginalProjCechOpen_intersection (R := R) G (cechTupleSupport t)).symm).op).hom
        ((Proj.awayToSection G (algebraMap (MvPolynomial ι R) S
          (projectiveLaurentDenominator R (cechTupleSupport t)))).hom
          ((gradedScalarAwayIso (R := R) G _).hom.hom
            (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G)
              (cechTupleSupport t) (a t)))) := by
  change ((Proj G).presheaf.map
      (eqToHom (congrArg op (gradedOriginalProjCechOpen_intersection (R := R) G
        (cechTupleSupport t))))).hom
      ((Proj.awayToSection G _).hom ((gradedScalarAwayIso (R := R) G _).hom.hom
        (projectiveHomogeneousChartLinearEquiv (gradedScalarComponents (R := R) G)
          (cechTupleSupport t) (a t)))) = _
  congr 2

end SerrePositivity.AlgebraicGeometry
