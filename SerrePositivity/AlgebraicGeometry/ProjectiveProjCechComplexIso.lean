module

public import SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarSections
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechNonemptyComparison

/-!
概要：斉次局所化で計算した Čech 複体を、実際の Proj の標準開の構造層へ移す。
方針：正の長さのタプルの非空交叉だけで、自然な R 線形同型を組み立てる。
規約：空交叉の環を零次成分と大域切断の間で同一視しない。
使われ方：有限性と形式関数の Čech 版を、被覆によらない比較へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R S : Type u} {ι : Type} [CommRing R] [CommRing S]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- Proj の変数に対応する実際の標準開の族。 -/
def projectiveProjCechOpen (i : ι) : (Proj G).Opens :=
  Proj.basicOpen G (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))

/-- 変数の像の積の標準開は、Čech の有限交叉と一致する。 -/
theorem projectiveProjCechOpen_intersection (T : Finset ι) :
    Proj.basicOpen G (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) =
      cechOpenIntersection (projectiveProjCechOpen (ι := ι) G) T := by
  rw [projectiveProjStandardOpen_eq_intersection]
  simp only [Finset.inf_eq_iInf, cechOpenIntersection, projectiveProjCechOpen]

/-- 非空交叉の斉次局所化と、構造層の実際の切断との R 線形同型。 -/
def projectiveProjCechSectionLinearEquiv (T : Finset ι) (hT : T.Nonempty) :
    (projectiveHomogeneousChartDiagram (ι := ι) G).obj T ≃ₗ[R]
      (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
          (projectiveProjCechOpen (ι := ι) G)).obj T :=
  (projectiveProjAwaySectionLinearEquiv G (projectivePolynomialDenominatorImage_mem G T)
      (Finset.card_pos.mpr hT)).trans
    (((schemeStructureCechPresheaf (Proj G) ⋙
      ModuleCat.restrictScalars (projectiveScalarToGlobalSections G)).mapIso
        (eqToIso (congrArg op (projectiveProjCechOpen_intersection G T)))).toLinearEquiv)

/-- 非空交叉の R 線形同型は、Čech の制限写像に自然。 -/
theorem projectiveProjCechSectionLinearEquiv_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveHomogeneousChartDiagram (ι := ι) G).map (homOfLE h) ≫
        (projectiveProjCechSectionLinearEquiv G U (hT.mono h)).toModuleIso.hom =
      (projectiveProjCechSectionLinearEquiv G T hT).toModuleIso.hom ≫
        (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
          ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
            (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let P := schemeStructureCechPresheaf (Proj G) ⋙
    ModuleCat.restrictScalars (projectiveScalarToGlobalSections G)
  change (P.map _).hom ((projectiveProjStandardSectionIso G U (hT.mono h)).hom.hom
      (((projectiveHomogeneousChartDiagram (ι := ι) G).map (homOfLE h)).hom z)) = _
  rw [projectiveProjStandardSectionIso_naturality]
  change (P.map _ ≫ P.map _).hom ((projectiveProjStandardSectionIso G T hT).hom.hom z) =
    (P.map _ ≫ P.map _).hom ((projectiveProjStandardSectionIso G T hT).hom.hom z)
  rw [← P.map_comp, ← P.map_comp]
  congr 2

/-- 斉次局所化で計算した Čech 複体と、実際の標準開の構造層の Čech 複体の同型。
原典 Stacks 30.2.6 のアフィン被覆の計算に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveProjNativeCechComplexIso :
    fullCechComplex (projectiveHomogeneousChartDiagram (ι := ι) G) ≅
      fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (projectiveScalarToGlobalSections G))
          (projectiveProjCechOpen (ι := ι) G)) :=
  fullCechNonemptyComplexIso
    (fun T hT ↦ (projectiveProjCechSectionLinearEquiv G T hT).toModuleIso)
    (fun hT h ↦ projectiveProjCechSectionLinearEquiv_naturality G hT h)

end SerrePositivity.AlgebraicGeometry
