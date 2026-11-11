module
public import SerrePositivity.KST.SConstruction.EnrichedCollageTransportComponents
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyCollageTransport
public import SerrePositivity.KST.SConstruction.LoopCollageCrossEvaluation

/-! # 元の固定構造射を全対象で持つ collage の円柱
概要：元の固定随伴構造射の交差辺を全成分として厳密に回収する。
方針：全体三角形の成分を計算し、離散頂点で同時に固定端点補正する。
規約：元の全入力 Ω 円柱と合成円柱の射の類を保持する。
使われ方：元の suspension 構造射を成分に持つ全入力円柱の構成。
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

/-- 元の指定随伴射の交差辺を全対象で厳密に回収する補正の存在証明。 -/
theorem boundaryAssemblyCollageCorrection {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    ∃ H' : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (boundaryPointedKanDiagram r F) ≫
        enrichedFunctorCollageBottomInfinity pointedKanLoopEnrichedFunctor)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (boundaryPointedKanDiagram (r + 1) F) ≫
        enrichedFunctorCollageTopInfinity pointedKanLoopEnrichedFunctor),
      (∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (enrichedFunctorCollageCross pointedKanLoopEnrichedFunctor
          (show (boundaryPointedKanDiagram r F).obj i ⟶
            pointedKanLoopObject ((boundaryPointedKanDiagram (r + 1) F).obj i) from
              ObjectProperty.homMk (boundaryKanAssemblyAdjoint r (F.obj i))))).edge) ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') =
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (boundaryAssemblyCollageHomotopy r F)) :=
  exists_enrichedFunctorCollageTransport_specified_components pointedKanLoopEnrichedFunctor
    (F := boundaryPointedKanDiagram r F) (G := boundaryPointedKanDiagram (r + 1) F)
    (boundaryAssemblyNativeOmegaHomotopy r F)
    (fun i => (show (boundaryPointedKanDiagram r F).obj i ⟶
      pointedKanLoopObject ((boundaryPointedKanDiagram (r + 1) F).obj i) from
        ObjectProperty.homMk (boundaryKanAssemblyAdjoint r (F.obj i))))
    (boundaryAssemblyNativeOmegaHomotopy_vertex_edge r F)

/-- 元の全対象の固定構造射の交差辺を持つ、同じ端点の全入力円柱。 -/
def boundaryAssemblySpecifiedCollageHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) := (boundaryAssemblyCollageCorrection r F).choose

/-- 補正した円柱は元の固定構造射の交差辺を厳密に回収する。 -/
lemma boundaryAssemblySpecifiedCollageHomotopy_vertex_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (boundaryAssemblySpecifiedCollageHomotopy r F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (loopCollageCrossMap ((boundaryPointedKanDiagram r F).obj i)
        ((boundaryPointedKanDiagram (r + 1) F).obj i)
          (boundaryKanAssemblyAdjoint r (F.obj i)))).edge := by
  have h := (boundaryAssemblyCollageCorrection r F).choose_spec.1 i
  have hc := enrichedFunctorCollageCross_loop ((boundaryPointedKanDiagram r F).obj i)
    ((boundaryPointedKanDiagram (r + 1) F).obj i) (boundaryKanAssemblyAdjoint r (F.obj i))
  rw [hc] at h
  exact h

/-- 補正は元の全体の合成円柱のホモトピー圏の射の類を保持する。 -/
lemma boundaryAssemblySpecifiedCollageHomotopy_hom {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (boundaryAssemblySpecifiedCollageHomotopy r F)) =
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (boundaryAssemblyCollageHomotopy r F)) :=
  (boundaryAssemblyCollageCorrection r F).choose_spec.2

end SerrePositivity.KST.SConstruction
