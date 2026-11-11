module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblySpecifiedCollage

/-! # 元の固定 suspension 構造射を成分に持つ全入力円柱
概要：元の構造射を全対象で厳密に持つ、suspension 側の全入力変換を構成する。
方針：局所 Kan な collage で補正した円柱を、全点つき模型の nerve へ評価する。
規約：元の suspension 模型を保持し、値域の quasicategory 性は使わない。
使われ方：元の BF 列の構造射を保持する coherent なスペクトル値関手化。
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
open scoped Simplicial
local instance boundaryOriginalSuspension_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の全対象の構造射に補正した全入力円柱を、元の suspension 模型の nerve へ評価する。 -/
def boundaryAssemblyOriginalSuspensionHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : SSet.Homotopy
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor)
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor (r + 1))
        (fun i => boundaryKanRealization_kanComplex (r + 1) (F.obj i)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (boundaryAssemblySpecifiedCollageHomotopy r F)
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

/-- 全入力の suspension 側の円柱の射は、collage の補正した円柱の全単体の評価。 -/
lemma boundaryAssemblyOriginalSuspensionHomotopy_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    (boundaryAssemblyOriginalSuspensionHomotopy r F).h =
      (boundaryAssemblySpecifiedCollageHomotopy r F).h ≫ loopCollageEvaluationNerve := rfl

/-- 全入力円柱の各成分は、元の固定 suspension 構造射の一単体を厳密に回収する。 -/
lemma boundaryAssemblyOriginalSuspensionHomotopy_vertex_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (boundaryAssemblyOriginalSuspensionHomotopy r F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (boundaryKanAssemblySigma r (F.obj i))).edge := by
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (boundaryAssemblyOriginalSuspensionHomotopy r F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
      loopCollageEvaluationNerve.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (boundaryAssemblySpecifiedCollageHomotopy r F)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge := rfl
  rw [boundaryAssemblySpecifiedCollageHomotopy_vertex_edge] at hv
  have he := enrichedNerveMap_edge loopCollageEvaluation
    (loopCollageCrossMap ((boundaryPointedKanDiagram r F).obj i)
      ((boundaryPointedKanDiagram (r + 1) F).obj i) (boundaryKanAssemblyAdjoint r (F.obj i)))
  have hc := loopCollageCrossMap_evaluation ((boundaryPointedKanDiagram r F).obj i)
    ((boundaryPointedKanDiagram (r + 1) F).obj i) (boundaryKanAssemblyAdjoint r (F.obj i))
  rw [hc] at he
  exact hv.trans he

end SerrePositivity.KST.SConstruction
