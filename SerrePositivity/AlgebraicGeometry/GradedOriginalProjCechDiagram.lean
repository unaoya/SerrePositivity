module

public import SerrePositivity.AlgebraicGeometry.CechDiagramTransport
public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimit
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
概要：動く基底の各段で元の Proj を使った、実際の Čech 複体の図式を作る。
方針：共通多項式環上の次数零局所化の図式を移し、遷移が実際の引き戻しと一致することを示す。
規約：スカラーの制限後も各段の Proj 自体を置き換えない。
使われ方：filtered colimit の比較を、極限先だけでなく各有限段の実際の切断へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry HomogeneousIdeal
universe u
variable {R : Type u} [CommRing R] {ι : Type} [LinearOrder ι] [Fintype ι]
variable {J : Type u} [SmallCategory J]
variable (C : J ⥤ CommAlgCat.{u} (MvPolynomial ι R))

/-- 次数付き環の図式を、共通の多項式環上の加群の図式として扱う。 -/
def gradedOriginalRingDiagramModule : J ⥤ ModuleCat.{u} (MvPolynomial ι R) :=
  C ⋙ forget₂ (CommAlgCat (MvPolynomial ι R)) (AlgCat (MvPolynomial ι R)) ⋙
    forget₂ (AlgCat (MvPolynomial ι R)) (ModuleCat (MvPolynomial ι R))

local instance originalRingDiagramBaseAlgebra (j : J) : Algebra R (C.obj j) :=
  Algebra.compHom (C.obj j) (algebraMap R (MvPolynomial ι R))
local instance originalRingDiagramBaseTower (j : J) :
    IsScalarTower R (MvPolynomial ι R) (C.obj j) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) (C.obj j)

variable {σ : J → Type u}
variable [∀ j, SetLike (σ j) (C.obj j)] [∀ j, AddSubgroupClass (σ j) (C.obj j)]
variable [∀ j, SMulMemClass (σ j) R (C.obj j)]
variable (G : ∀ j, ℕ → σ j) [∀ j, GradedRing (G j)]
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]
variable (hG : ∀ {i j} (f : i ⟶ j) (n : ℕ) (m : C.obj i),
  m ∈ G i n → (C.map f).hom m ∈ G j n)

include hG in
/-- 元の各段の grading の、環の遷移に沿う次数付き環の射。 -/
def gradedOriginalRingDiagramMap {i j : J} (f : i ⟶ j) : G i →+*ᵍ G j where
  toRingHom := (C.map f).hom.toRingHom
  map_mem := hG f _ _

/-- 共通基底上の次数零チャートの、遷移を含めた係数図式。 -/
def gradedOriginalRingChartDiagram : J ⥤ (Finset ι ⥤ ModuleCat.{u} R) :=
  projectiveNatChartColimitDiagram (gradedOriginalRingDiagramModule C)
    (fun j ↦ gradedScalarComponents (R := R) (G j)) hG 0

/-- 各段で元の Proj の構造層を使う、実際の Čech 複体の図式。 -/
def gradedOriginalProjNativeCechDiagram : J ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  cechDiagramTransport (gradedOriginalRingChartDiagram C G hG ⋙ fullCechComplexFunctor)
    (fun j ↦ fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj (G j)) ⋙
      ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections (R := R) (G j)))
        (gradedOriginalProjCechOpen (R := R) (ι := ι) (G j))))
    (fun j ↦ gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) (G j))

/-- 各段だけでなく、図式全体での次数零チャートと元の Proj の自然同型。 -/
def gradedOriginalProjNativeCechDiagramIso :
    gradedOriginalRingChartDiagram C G hG ⋙ fullCechComplexFunctor ≅
      gradedOriginalProjNativeCechDiagram C G hG :=
  cechDiagramTransportIso _ _ _

/-- 移した図式の遷移は、元の Proj の実際の構造層の引き戻しそのもの。 -/
theorem gradedOriginalProjNativeCechDiagram_map {i j : J} (f : i ⟶ j)
    (hf : irrelevant (G j) ≤ (irrelevant (G i)).map (gradedOriginalRingDiagramMap C G hG f)) :
    (gradedOriginalProjNativeCechDiagram C G hG).map f =
      gradedOriginalProjNativeCechMap (G i) (G j) (gradedOriginalRingDiagramMap C G hG f)
        (C.map f).hom (fun _ ↦ rfl) hf := by
  change (gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) (G i)).inv ≫
      fullCechComplexMap (projectiveNatGradedModuleChartMap
        (gradedScalarComponents (R := R) (G i)) (gradedScalarComponents (R := R) (G j))
          (C.map f).hom.toLinearMap (hG f) 0) ≫
      (gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) (G j)).hom = _
  rw [gradedOriginalProjNativeCechComplexIso_naturality (G i) (G j)
    (gradedOriginalRingDiagramMap C G hG f) (C.map f).hom (fun _ ↦ rfl) hf]
  simp only [Iso.inv_hom_id_assoc]

end SerrePositivity.AlgebraicGeometry
