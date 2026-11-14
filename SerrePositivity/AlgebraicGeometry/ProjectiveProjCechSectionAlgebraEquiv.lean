module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousChartAlgebra
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjCechComplexIso
public import SerrePositivity.AlgebraicGeometry.SchemeSectionAlgebraCech

/-!
概要：非空の標準開の交叉の線形比較を、実際の切断環の代数同型にする。
方針：Proj.awayToSection と開集合の等式による制限が積を保つことを使う。
規約：空交叉にはこの同型を主張しない。
使われ方：F7 の斉次局所化の適合切断と構造層の適合切断の環としての比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 非空の標準開の交叉上の、実際の構造層との代数同型。 -/
def projectiveProjCechSectionAlgEquiv (T : Finset ι) (hT : T.Nonempty) :
    (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T ≃ₐ[R]
      (schemeSectionAlgebraCechDiagram (Proj G) (projectiveScalarToGlobalSections G)
        (projectiveProjCechOpen (ι := ι) G)).obj T :=
  { projectiveProjCechSectionLinearEquiv G T hT with
    map_mul' := by
      intro x y
      change ((Proj G).presheaf.map _).hom ((Proj.awayToSection G _).hom (x * y)) =
        ((Proj G).presheaf.map _).hom ((Proj.awayToSection G _).hom x) *
          ((Proj G).presheaf.map _).hom ((Proj.awayToSection G _).hom y)
      rw [map_mul, map_mul]
    commutes' := by
      intro r
      have h1 : projectiveProjCechSectionLinearEquiv G T hT
          (1 : (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T) =
          (1 : (schemeSectionAlgebraCechDiagram (Proj G)
            (projectiveScalarToGlobalSections G) (projectiveProjCechOpen G)).obj T) := by
        change ((Proj G).presheaf.map _).hom ((Proj.awayToSection G _).hom 1) = 1
        rw [map_one, map_one]
      change projectiveProjCechSectionLinearEquiv G T hT
        (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T) r) =
        algebraMap R ((schemeSectionAlgebraCechDiagram (Proj G)
          (projectiveScalarToGlobalSections G) (projectiveProjCechOpen G)).obj T) r
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1,
        Algebra.algebraMap_eq_smul_one] }

/-- 代数同型の線形写像は、既存の Čech 複体の比較そのもの。 -/
theorem projectiveProjCechSectionAlgEquiv_apply (T : Finset ι) (hT : T.Nonempty)
    (x : (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T) :
    projectiveProjCechSectionAlgEquiv G T hT x =
      projectiveProjCechSectionLinearEquiv G T hT x := rfl

/-- 非空交叉の代数同型は、実際の制限写像と可換。 -/
theorem projectiveProjCechSectionAlgEquiv_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U)
    (x : (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj T) :
    projectiveProjCechSectionAlgEquiv G U (hT.mono h)
      (((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).map (homOfLE h)).hom x) =
    ((schemeSectionAlgebraCechDiagram (Proj G) (projectiveScalarToGlobalSections G)
      (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h)).hom
        (projectiveProjCechSectionAlgEquiv G T hT x) :=
  congrArg (fun f ↦ f.hom x) (projectiveProjCechSectionLinearEquiv_naturality G hT h)

end SerrePositivity.AlgebraicGeometry
