module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitIso
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedColimitNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredNaturality

/-!
概要：実際の標準開の余極限比較を、次数を保つ図式の射に自然にする。
方針：有限段からの写像で colimit の射を比較する。
規約：共通の基底と多項式変数を固定する。
使われ方：底変換・閉厚化などの図式の射と余極限比較の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (M N : J ⥤ ModuleCat.{u} (MvPolynomial ι R))
local instance natChartColimitNaturalBaseModule (V : ModuleCat.{u} (MvPolynomial ι R)) :
    Module R V := Module.compHom V (algebraMap R (MvPolynomial ι R))
local instance natChartColimitNaturalBaseTower (V : ModuleCat.{u} (MvPolynomial ι R)) :
    IsScalarTower R (MvPolynomial ι R) V :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) V
variable (G : ∀ j, ℕ → Submodule R (M.obj j))
variable (H : ∀ j, ℕ → Submodule R (N.obj j))
variable (hG : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : M.obj i),
  m ∈ G i n → (M.map α).hom m ∈ G j n)
variable (hH : ∀ {i j} (α : i ⟶ j) (n : ℕ) (m : N.obj i),
  m ∈ H i n → (N.map α).hom m ∈ H j n)
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (H j)]
variable (η : M ⟶ N)
variable (hη : ∀ j n (m : M.obj j), m ∈ G j n → (η.app j).hom m ∈ H j n)

/-- 次数を保つ図式の射が誘導する、標準開の filtered 図式の射。 -/
def projectiveNatChartColimitDiagramMap (d : ℤ) :
    projectiveNatChartColimitDiagram M G hG d ⟶
      projectiveNatChartColimitDiagram N H hH d where
  app j := projectiveNatGradedModuleChartMap (G j) (H j) (η.app j).hom (hη j) d
  naturality {i j} α := by
    change projectiveNatGradedModuleChartMap (G i) (G j) (M.map α).hom (hG α) d ≫
      projectiveNatGradedModuleChartMap (G j) (H j) (η.app j).hom (hη j) d =
        projectiveNatGradedModuleChartMap (G i) (H i) (η.app i).hom (hη i) d ≫
          projectiveNatGradedModuleChartMap (H i) (H j) (N.map α).hom (hH α) d
    rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
    congr 1
    exact congrArg ModuleCat.Hom.hom (η.naturality α)

/-- 図式の射の余極限が誘導する、余極限の実際の標準開の射。 -/
def projectiveNatChartColimitTargetMap (d : ℤ) :
    (projectiveNatChartColimitCocone M G hG d).pt ⟶
      (projectiveNatChartColimitCocone N H hH d).pt :=
  letI := projectiveGradedColimitGradeGradedSMul M G hG
    (MvPolynomial.homogeneousSubmodule ι R)
  letI := projectiveGradedColimitGradeGradedSMul N H hH
    (MvPolynomial.homogeneousSubmodule ι R)
  projectiveNatGradedModuleChartMap (projectiveGradedColimitGrade M G)
    (projectiveGradedColimitGrade N H) (colim.map η).hom
    (projectiveGradedColimitMap_preservesPiece M N G H hG hH η hη) d

/-- 実際の標準開の比較射は、次数を保つ図式の射に自然。 -/
theorem projectiveNatChartColimitMap_naturality (d : ℤ) :
    colim.map (projectiveNatChartColimitDiagramMap M N G H hG hH η hη d) ≫
        projectiveNatChartColimitMap N H hH d =
      projectiveNatChartColimitMap M G hG d ≫
        projectiveNatChartColimitTargetMap M N G H hG hH η hη d := by
  letI := projectiveGradedColimitGradeGradedSMul M G hG
    (MvPolynomial.homogeneousSubmodule ι R)
  letI := projectiveGradedColimitGradeGradedSMul N H hH
    (MvPolynomial.homogeneousSubmodule ι R)
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_map_assoc]
  simp only [projectiveNatChartColimitMap, colimit.ι_desc, colimit.ι_desc_assoc]
  change projectiveNatGradedModuleChartMap (G j) (H j) (η.app j).hom (hη j) d ≫
      projectiveNatGradedModuleChartMap (H j) (projectiveGradedColimitGrade N H)
        (colimit.ι N j).hom (projectiveGradedColimitInclusion_preservesPiece N H hH j) d =
    projectiveNatGradedModuleChartMap (G j) (projectiveGradedColimitGrade M G)
      (colimit.ι M j).hom (projectiveGradedColimitInclusion_preservesPiece M G hG j) d ≫
        projectiveNatGradedModuleChartMap (projectiveGradedColimitGrade M G)
          (projectiveGradedColimitGrade N H) (colim.map η).hom
            (projectiveGradedColimitMap_preservesPiece M N G H hG hH η hη) d
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1
  exact (congrArg ModuleCat.Hom.hom (colimit.ι_map η j)).symm

/-- 実際の射影標準開の Čech H の余極限比較は、次数を保つ図式の射に自然。
原典 Stacks 30.6.1 の Hⁱ の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatCechFilteredHomologyIso_naturality (d : ℤ) (q : ℕ) :
    (fullCechComplexFunctor (R := R) (ι := ι) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (projectiveNatChartColimitTargetMap M N G H hG hH η hη d) ≫
          (projectiveNatCechFilteredHomologyIso N H hH d q).hom =
      (projectiveNatCechFilteredHomologyIso M G hG d q).hom ≫
        colim.map (Functor.whiskerRight
          (projectiveNatChartColimitDiagramMap M N G H hG hH η hη d)
          (fullCechComplexFunctor ⋙
            HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q)) := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let a := projectiveNatChartColimitDiagramMap M N G H hG hH η hη d
  let b := projectiveNatChartColimitTargetMap M N G H hG hH η hη d
  let eM := projectiveNatChartColimitIso M G hG d
  let eN := projectiveNatChartColimitIso N H hH d
  have hi : b ≫ eN.inv = eM.inv ≫ colim.map a := by
    apply (cancel_mono eN.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show colim.map a ≫ eN.hom = eM.hom ≫ b from
      projectiveNatChartColimitMap_naturality M N G H hG hH η hη d]
    simp only [Iso.inv_hom_id_assoc]
  change K.map b ≫ K.map eN.inv ≫
      (projectiveCechFilteredHomologyIso (projectiveNatChartColimitDiagram N H hH d) q).hom =
    (K.map eM.inv ≫
      (projectiveCechFilteredHomologyIso (projectiveNatChartColimitDiagram M G hG d) q).hom) ≫ _
  rw [← K.map_comp_assoc, hi, K.map_comp_assoc]
  have hn : K.map (colim.map a) ≫
      (projectiveCechFilteredHomologyIso (projectiveNatChartColimitDiagram N H hH d) q).hom =
    (projectiveCechFilteredHomologyIso (projectiveNatChartColimitDiagram M G hG d) q).hom ≫
      colim.map (Functor.whiskerRight a K) :=
    projectiveCechFilteredHomologyIso_naturality a q
  simpa only [Category.assoc] using congrArg (fun f ↦ K.map eM.inv ≫ f) hn

end SerrePositivity.AlgebraicGeometry
