module
public import SerrePositivity.KST.SConstruction.EnrichedCollageTransport
public import SerrePositivity.KST.SConstruction.LoopCollageEvaluation
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyNativeOmega

/-! # 元の Ω 円柱から suspension 側への全入力移送
概要：元の全入力 Ω 円柱を局所 Kan な collage 内で合成し、suspension 側へ評価する。
方針：下段包含と交差恒等射の比較を実三角形で合成し、全単体の評価で写す。
規約：全点つき対象の nerve の quasicategory 性は使わない。成分の厳密な補正は別工程。
使われ方：元の固定構造射を成分に戻す補正と、BF の列の高次の厳密化への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories

local instance boundaryCollageTransport_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の Ω 円柱を、下段の元の段から上段の次段への全入力円柱に合成する。 -/
def boundaryAssemblyCollageHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : SSet.Homotopy
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)) ≫
          enrichedFunctorCollageBottomInfinity pointedKanLoopEnrichedFunctor)
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor (r + 1))
        (fun i => boundaryKanRealization_kanComplex (r + 1) (F.obj i)) ≫
          enrichedFunctorCollageTopInfinity pointedKanLoopEnrichedFunctor) :=
  enrichedFunctorCollageTransportHomotopy pointedKanLoopEnrichedFunctor
    (F := boundaryPointedKanDiagram r F) (G := boundaryPointedKanDiagram (r + 1) F)
    (boundaryAssemblyNativeOmegaHomotopy r F)

/-- 元の Ω 円柱の下段像・交差恒等射の比較・合成した円柱を保持する実三角形。 -/
def boundaryAssemblyCollageTriangle {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (enrichedFunctorCollageInputHomotopy pointedKanLoopEnrichedFunctor
        (boundaryAssemblyNativeOmegaHomotopy r F))
      (enrichedFunctorCollageComparisonHomotopy pointedKanLoopEnrichedFunctor
        (boundaryPointedKanDiagram (r + 1) F))
      (boundaryAssemblyCollageHomotopy r F) :=
  enrichedFunctorCollageTransportTriangle pointedKanLoopEnrichedFunctor
    (F := boundaryPointedKanDiagram r F) (G := boundaryPointedKanDiagram (r + 1) F)
    (boundaryAssemblyNativeOmegaHomotopy r F)

/-- Collage 内の合成した全入力円柱を、元の suspension 模型の nerve へ評価する。 -/
def boundaryAssemblySuspensionTransportHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : SSet.Homotopy
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor)
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor (r + 1))
        (fun i => boundaryKanRealization_kanComplex (r + 1) (F.obj i)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (boundaryAssemblyCollageHomotopy r F)
    loopCollageEvaluationNerve
  refine { h := H.h, h₀ := H.h₀.trans ?_, h₁ := H.h₁.trans ?_, rel := ?_ }
  · rw [Category.assoc, loopCollageEvaluationNerve_bottom]
    rfl
  · rw [Category.assoc, loopCollageEvaluationNerve_top]
    rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 全入力の suspension 側の円柱の射は、collage の合成した円柱の全単体の評価。 -/
lemma boundaryAssemblySuspensionTransportHomotopy_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    (boundaryAssemblySuspensionTransportHomotopy r F).h =
      (boundaryAssemblyCollageHomotopy r F).h ≫ loopCollageEvaluationNerve := rfl

end SerrePositivity.KST.SConstruction
