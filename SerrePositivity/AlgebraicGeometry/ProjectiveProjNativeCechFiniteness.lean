module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjCechComplexIso
public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechScalarHomology
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
概要：射影の有限性を、実際の構造層の任意の有限アフィン被覆の Čech H に移す。
方針：斉次局所化の複体と標準開の複体を同一視し、共通アフィン細分で被覆を変更する。
規約：基底環は元の R、空交叉の切断を零次成分と同一視しない。
使われ方：BST13 Lemma 3.9 に必要な射影 Čech 版の有限性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 指定次数の代数的な複体から、実際の Proj の標準開への比較。 -/
def projectiveProjNativeNatCechComplexIso :
    fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G 0) ≅
      fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
          (projectiveProjCechOpen (ι := ι) G)) :=
  fullCechComplexFunctor.mapIso (projectiveHomogeneousChartDiagramIso (ι := ι) G) ≪≫
    projectiveProjNativeCechComplexIso G

/-- 実際の Proj の構造層の標準開 Čech H の有限性。
原典 Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveProjNativeStandardCechHomology_finite
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S] (q : ℕ) :
    Module.Finite R ((fullCechComplex (openCoverCechDiagram
      (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
          (projectiveProjCechOpen (ι := ι) G))).homology q) := by
  let e := (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q).mapIso
    (projectiveProjNativeNatCechComplexIso (ι := ι) G)
  letI : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q).obj
        (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G 0))) := by
    change Module.Finite R
      ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G 0)).homology q)
    exact projectiveNatGradedFullCechHomology_finite (ι := ι) G 0 q
  exact Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)

/-- 実際の Proj の構造層の、任意の有限アフィン被覆での Čech H の有限性。
原典 Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveProjNativeAffineCechHomology_finite
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S]
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))))
    {κ : Type} [LinearOrder κ] [Fintype κ]
    (V : κ → (Proj G).Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hcV : (⨆ j, V j) = ⊤) (q : ℕ) :
    Module.Finite R ((fullCechComplex (openCoverCechDiagram
      (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G)) V)).homology q) := by
  let U := projectiveProjCechOpen (ι := ι) G
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦
    Proj.isAffineOpen_basicOpen G _ (projectivePolynomialVariableImage_mem G i) Nat.zero_lt_one
  have hcU : (⨆ i, U i) = ⊤ := Proj.iSup_basicOpen_eq_top G _ hspan
  let e := schemeModuleCommonAffineCechScalarHomologyIso (projectiveScalarToGlobalSections G)
    (schemeStructureModule (Proj G)) U V hU hV hcU hcV q
  letI := projectiveProjNativeStandardCechHomology_finite (ι := ι) G q
  exact Module.Finite.of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)

end SerrePositivity.AlgebraicGeometry
