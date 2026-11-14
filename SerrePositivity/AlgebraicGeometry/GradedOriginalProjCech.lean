module

public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjSections
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjNativeCechFiniteness

/-!
概要：基底環の違う次数成分を正規化しても、元の Proj の実際の切断を計算する。
方針：同じ carrier の斉次局所化の同型を使い、元の Proj の標準開へ移す。
規約：Proj 自体を別の grading の Proj と同一視せず、空交叉も同一視しない。
使われ方：動く基底環の各段の Čech 複体を共通の基底環上で比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u v
variable {R S : Type u} {σ : Type v} {ι : Type}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [SetLike σ S] [AddSubgroupClass σ S] [SMulMemClass σ R S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → σ) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- scalar の指定の前の、元の Proj の標準開。 -/
def gradedOriginalProjCechOpen (i : ι) : (Proj G).Opens :=
  Proj.basicOpen G (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))

/-- 元の Proj の標準開の交叉は、変数の像の積での標準開。 -/
theorem gradedOriginalProjCechOpen_intersection (T : Finset ι) :
    Proj.basicOpen G (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) =
      cechOpenIntersection (gradedOriginalProjCechOpen (R := R) (ι := ι) G) T := by
  rw [projectivePolynomialDenominatorImage,
    proj_basicOpen_finset_prod]
  simp only [Finset.inf_eq_iInf, cechOpenIntersection, gradedOriginalProjCechOpen]

/-- carrier の正規化前の実際の標準開へ、非空交叉の係数を移す線形同型。 -/
def gradedOriginalProjCechSectionLinearEquiv (T : Finset ι) (hT : T.Nonempty) :
    (projectiveHomogeneousChartDiagram (ι := ι) (gradedScalarComponents (R := R) G)).obj T ≃ₗ[R]
      (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections G))
          (gradedOriginalProjCechOpen (R := R) (ι := ι) G)).obj T :=
  ((gradedScalarAwayLinearEquiv (R := R) G
      (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T))).trans
    (gradedOriginalProjAwaySectionLinearEquiv G
      (projectivePolynomialDenominatorImage_mem (gradedScalarComponents (R := R) G) T)
      (Finset.card_pos.mpr hT))).trans
    (((schemeStructureCechPresheaf (Proj G) ⋙
      ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections G)).mapIso
        (eqToIso (congrArg op (gradedOriginalProjCechOpen_intersection (R := R) G T)))).toLinearEquiv)

/-- carrier の正規化前の切断への比較は、標準開を狭める射に自然。 -/
theorem gradedOriginalProjCechSectionLinearEquiv_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveHomogeneousChartDiagram (ι := ι) (gradedScalarComponents (R := R) G)).map
        (homOfLE h) ≫ (gradedOriginalProjCechSectionLinearEquiv (R := R) G U (hT.mono h)).toModuleIso.hom =
      (gradedOriginalProjCechSectionLinearEquiv (R := R) G T hT).toModuleIso.hom ≫
        (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
          ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections G))
            (gradedOriginalProjCechOpen (R := R) (ι := ι) G)).map (homOfLE h) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  change ((Proj G).presheaf.map _).hom
      ((Proj.awayToSection G _).hom
        ((gradedScalarAwayIso (R := R) G _).hom.hom
          (((projectiveHomogeneousChartDiagram (ι := ι)
            (gradedScalarComponents (R := R) G)).map (homOfLE h)).hom z))) = _
  rw [projectiveHomogeneousChartDiagram_map]
  change ((Proj G).presheaf.map _).hom
      ((Proj.awayToSection G _).hom
        ((gradedScalarAwayIso (R := R) G _).hom.hom
          (HomogeneousLocalization.awayMap (gradedScalarComponents (R := R) G) _ _ z))) = _
  rw [gradedScalarAwayIso_awayMap]
  have hn := Proj.awayMap_awayToSection G
    (show algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R (U \ T)) ∈
      G (U \ T).card from
        projectivePolynomialDenominatorImage_mem (gradedScalarComponents (R := R) G) (U \ T))
    (projectivePolynomialDenominatorImage_factor (R := R) (S := S) h)
  have hv := congrArg
    (fun k : CommRingCat.of (HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T))) ⟶
        Γ(Proj G, Proj.basicOpen G
          (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R U))) ↦
      k.hom ((gradedScalarAwayIso (R := R) G _).hom.hom z)) hn
  erw [hv]
  change ((Proj G).presheaf.map _ ≫ (Proj G).presheaf.map _).hom
      ((Proj.awayToSection G _).hom ((gradedScalarAwayIso (R := R) G _).hom.hom z)) =
    ((Proj G).presheaf.map _ ≫ (Proj G).presheaf.map _).hom
      ((Proj.awayToSection G _).hom ((gradedScalarAwayIso (R := R) G _).hom.hom z))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

/-- 共通の係数環上の標準開計算と、元の Proj の Čech 複体の同型。
原典 Stacks 30.2.6 のアフィン被覆の計算に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def gradedOriginalProjNativeCechComplexIso :
    fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (gradedScalarComponents (R := R) G) 0) ≅
      fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections G))
          (gradedOriginalProjCechOpen (R := R) (ι := ι) G)) :=
  fullCechComplexFunctor.mapIso
    (projectiveHomogeneousChartDiagramIso (ι := ι) (gradedScalarComponents (R := R) G)) ≪≫
      fullCechNonemptyComplexIso
        (fun T hT ↦ (gradedOriginalProjCechSectionLinearEquiv (R := R) G T hT).toModuleIso)
        (fun hT h ↦ gradedOriginalProjCechSectionLinearEquiv_naturality (R := R) G hT h)

end SerrePositivity.AlgebraicGeometry
