module

public import SerrePositivity.AlgebraicGeometry.GradedOriginalProjSections
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechRestrictScalars
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechFunctor

/-!
概要：元の Proj の切断を、段ごとの基底環と共通の基底環の両方で比較する。
方針：大域スカラーの合成の式と、スカラー制限の自然同型を合成する。
規約：同じ Proj と同じ開被覆を使い、スキームの型を置き換えない。
使われ方：動く係数環の標準開の比較を、共通係数での filtered colimit へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {R₀ R S : Type u} {σ : Type v}
variable [CommRing R₀] [CommRing R] [CommRing S]
variable [Algebra R₀ R] [Algebra R S] [Algebra R₀ S] [IsScalarTower R₀ R S]
variable [SetLike σ S] [AddSubgroupClass σ S]
variable [hR : SMulMemClass σ R S] [hR₀ : SMulMemClass σ R₀ S]
variable (G : ℕ → σ) [GradedRing G]

/-- 段の基底環での構造層の係数を制限すると、共通の基底環での係数と自然に同型。 -/
def gradedOriginalProjCoefficientScalarIso :
    schemeStructureCechPresheaf (Proj G) ⋙ ModuleCat.restrictScalars
      (gradedOriginalScalarToGlobalSections (R := R₀) (hR := hR₀) G) ≅
    (schemeStructureCechPresheaf (Proj G) ⋙ ModuleCat.restrictScalars
      (gradedOriginalScalarToGlobalSections (R := R) (hR := hR) G)) ⋙
        ModuleCat.restrictScalars (algebraMap R₀ R) :=
  Functor.isoWhiskerLeft (schemeStructureCechPresheaf (Proj G))
    (ModuleCat.restrictScalarsComp' (algebraMap R₀ R)
      (gradedOriginalScalarToGlobalSections (R := R) (hR := hR) G)
      (gradedOriginalScalarToGlobalSections (R := R₀) (hR := hR₀) G)
      (gradedOriginalScalarToGlobalSections_comp (hR := hR) (hR₀ := hR₀) G))

variable {ι : Type} [DecidableEq ι] (U : ι → (Proj G).Opens)

/-- 段ごとの基底環の制限と、同じ実際の Proj の Čech 複体の比較。 -/
def gradedOriginalProjCechScalarRestrictionIso :
    fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
      ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections
        (R := R₀) (hR := hR₀) G)) U) ≅
    ((ModuleCat.restrictScalars (algebraMap R₀ R)).mapHomologicalComplex (.up ℕ)).obj
      (fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
        ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections
          (R := R) (hR := hR) G)) U)) :=
  fullCechComplexFunctor.mapIso ((openCoverCechDiagramFunctor U).mapIso
    (gradedOriginalProjCoefficientScalarIso (hR := hR) (hR₀ := hR₀) G)) ≪≫
      projectiveCechRestrictScalarsComplexIso (algebraMap R₀ R)
        (openCoverCechDiagram (schemeStructureCechPresheaf (Proj G) ⋙
          ModuleCat.restrictScalars (gradedOriginalScalarToGlobalSections
            (R := R) (hR := hR) G)) U)

end SerrePositivity.AlgebraicGeometry
