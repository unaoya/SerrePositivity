module

public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjCechDiagram
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatChartColimitTarget

/-!
概要：動く基底の各段と極限先の両方で、元の Proj の実際の Čech H を比較する。
方針：実際の各段の複体の自然同型を、H と filtered colimit へ移す。
規約：有限型模型・環と次数の余極限の構成は 2g の入力であり、ここでは明示する。
使われ方：元の基底環から制限した各段の H を、実際の極限先の H へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {ι : Type} [LinearOrder ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (C : J ⥤ CommAlgCat.{u} (MvPolynomial ι R))
local instance originalFilteredStageAlgebra (j : J) : Algebra R (C.obj j) :=
  Algebra.compHom (C.obj j) (algebraMap R (MvPolynomial ι R))
local instance originalFilteredStageTower (j : J) :
    IsScalarTower R (MvPolynomial ι R) (C.obj j) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) (C.obj j)
local instance originalFilteredColimitModule :
    Module R (colimit (gradedOriginalRingDiagramModule C) : ModuleCat.{u} (MvPolynomial ι R)) :=
  Module.compHom (colimit (gradedOriginalRingDiagramModule C) : ModuleCat.{u} (MvPolynomial ι R))
    (algebraMap R (MvPolynomial ι R))
local instance originalFilteredColimitTower :
    IsScalarTower R (MvPolynomial ι R)
      (colimit (gradedOriginalRingDiagramModule C) : ModuleCat.{u} (MvPolynomial ι R)) :=
  IsScalarTower.of_compHom R (MvPolynomial ι R)
    (colimit (gradedOriginalRingDiagramModule C) : ModuleCat.{u} (MvPolynomial ι R))
variable {σ : J → Type u}
variable [∀ j, SetLike (σ j) (C.obj j)] [∀ j, AddSubgroupClass (σ j) (C.obj j)]
variable [∀ j, SMulMemClass (σ j) R (C.obj j)]
variable (G : ∀ j, ℕ → σ j) [∀ j, GradedRing (G j)]
variable [∀ j, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G j)]
variable (hG : ∀ {i j} (f : i ⟶ j) (n : ℕ) (m : C.obj i),
  m ∈ G i n → (C.map f).hom m ∈ G j n)
variable (T : CommAlgCat.{u} (MvPolynomial ι R))
local instance originalFilteredTargetAlgebra : Algebra R T :=
  Algebra.compHom T (algebraMap R (MvPolynomial ι R))
local instance originalFilteredTargetTower : IsScalarTower R (MvPolynomial ι R) T :=
  IsScalarTower.of_compHom R (MvPolynomial ι R) T
variable {τ : Type u} [SetLike τ T] [AddSubgroupClass τ T] [SMulMemClass τ R T]
variable (H : ℕ → τ) [GradedRing H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (e : (colimit (gradedOriginalRingDiagramModule C) : ModuleCat.{u} (MvPolynomial ι R)) ≃ₗ[MvPolynomial ι R] T)
variable (he : ∀ n x, e x ∈ H n ↔ x ∈ projectiveGradedColimitGrade
  (gradedOriginalRingDiagramModule C) (fun j ↦ gradedScalarComponents (R := R) (G j)) n)

/-- 各段と極限先の両方で、元の Proj の実際の構造層を使う filtered Čech H の比較。
原典 Stacks 30.6.1 の Hⁱ の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。模型と余極限の存在は、この宣言の主張に含めない。 -/
def gradedOriginalProjNativeFilteredHomologyIso (q : ℕ) :
    (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj H) ⋙
      ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections (R := R) H))
        (gradedOriginalProjCechOpen (R := R) (ι := ι) H))).homology q ≅
      colimit (gradedOriginalProjNativeCechDiagram C G hG ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
      (gradedOriginalProjNativeCechComplexIso (R := R) (ι := ι) H).symm ≪≫
    projectiveNatCechFilteredHomologyTargetIso (gradedOriginalRingDiagramModule C)
      (fun j ↦ gradedScalarComponents (R := R) (G j)) hG
      (gradedScalarComponents (R := R) H) e he 0 q ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerRight (gradedOriginalProjNativeCechDiagramIso C G hG)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q))

end SerrePositivity.AlgebraicGeometry
