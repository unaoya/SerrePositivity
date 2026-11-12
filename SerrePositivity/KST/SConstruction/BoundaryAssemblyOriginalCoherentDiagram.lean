module
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyCoherentOmegaCondition
public import SerrePositivity.KST.SConstruction.PointedKanSpecifiedComponentCorrection

/-! # 元の構造射を全対象で厳密に回収する coherent な Ω 比較
概要：元の選択構造射を全対象の成分に同時に固定し、全入力単体の変換を構成する。
方針：元の構造射との成分一致を、離散頂点上の固定端点の補正へ渡す。
規約：元の Kan 模型・元の構造射・全体の変換の射の類を保つ。入力は小さい通常の圏。
使われ方：元の BF K の構造射を保持する全射列の自然性と、列の厳密化への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 任意の元の選択射の族を全対象の成分として厳密に回収する全体変換が存在する。 -/
lemma exists_boundaryAssemblySpecifiedCoherentHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u})
    (v : ∀ i, (boundaryKanAssemblyChoices r (F.obj i)) _⦋0⦌) :
    ∃ H : SSet.Homotopy
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)))
      (pointedKanCoherentDiagram (F ⋙ loopBoundaryKanFunctor (r + 1))
        (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))),
      (∀ i, pointedKanDiagramHomotopyMapAt
        (fun j => boundaryKanRealization_kanComplex r (F.obj j))
        (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j)) H i =
          boundaryKanAssemblyAdjointAt r (F.obj i) (v i)) ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (boundaryAssemblyCoherentDiagramHomotopy r F)) :=
  exists_pointedKanDiagram_specified_components
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (boundaryAssemblyCoherentDiagramHomotopy r F) (fun i => boundaryKanAssemblyAdjointAt r (F.obj i) (v i))
    (fun i => (boundaryAssemblyCoherentDiagramMapAt_component r F i (v i)).symm)

/-- 固定された元の構造射を全対象で厳密に回収する全体変換が存在する。 -/
lemma exists_boundaryAssemblyOriginalCoherentHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    ∃ H : SSet.Homotopy
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)))
      (pointedKanCoherentDiagram (F ⋙ loopBoundaryKanFunctor (r + 1))
        (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))),
      (∀ i, pointedKanDiagramHomotopyMapAt
        (fun j => boundaryKanRealization_kanComplex r (F.obj j))
        (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j)) H i = boundaryKanAssemblyAdjoint r (F.obj i)) ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (boundaryAssemblyCoherentDiagramHomotopy r F)) :=
  exists_pointedKanDiagram_specified_components
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (boundaryAssemblyCoherentDiagramHomotopy r F) (fun i => boundaryKanAssemblyAdjoint r (F.obj i))
    (fun i => (boundaryAssemblyCoherentDiagramMapAt_original_component r F i).symm)

/-- 元の構造射を厳密な成分として持つ、全射列の coherent な変換。 -/
def boundaryAssemblyOriginalCoherentHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :=
  (exists_boundaryAssemblyOriginalCoherentHomotopy r F).choose

/-- 全体変換の成分を回収すると、元の固定構造射そのものになる。 -/
lemma boundaryAssemblyOriginalCoherentHomotopy_component {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    pointedKanDiagramHomotopyMapAt
      (fun j => boundaryKanRealization_kanComplex r (F.obj j))
      (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j))
      (boundaryAssemblyOriginalCoherentHomotopy r F) i = boundaryKanAssemblyAdjoint r (F.obj i) :=
  (exists_boundaryAssemblyOriginalCoherentHomotopy r F).choose_spec.1 i

/-- 補正した全体変換の射の類は、元の全体変換の射の類を保つ。 -/
lemma boundaryAssemblyOriginalCoherentHomotopy_hom {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (boundaryAssemblyOriginalCoherentHomotopy r F)) =
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (boundaryAssemblyCoherentDiagramHomotopy r F)) :=
  (exists_boundaryAssemblyOriginalCoherentHomotopy r F).choose_spec.2

/-- 補正後の全体変換の対象での辺は、元の構造射の coherent な辺の一単体そのもの。 -/
lemma boundaryAssemblyOriginalCoherentHomotopy_vertex_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (boundaryAssemblyOriginalCoherentHomotopy r F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (boundaryPointedKanDiagram r F).obj i ⟶
      (pointedKanDiagram (F ⋙ loopBoundaryKanFunctor (r + 1))
        (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j))).obj i from
          ObjectProperty.homMk (boundaryKanAssemblyAdjoint r (F.obj i)))).edge := by
  have he := pointedKanDiagramHomotopyMapAt_edge
    (fun j => boundaryKanRealization_kanComplex r (F.obj j))
    (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j))
    (boundaryAssemblyOriginalCoherentHomotopy r F) i
  rw [boundaryAssemblyOriginalCoherentHomotopy_component] at he
  exact he.symm

/-- 元の構造射を厳密に保持する指定した全体変換は、図式全体の Ω 比較同型。 -/
def boundaryAssemblyOriginalCoherentIso {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :=
  pointedKanDiagramHomotopyFunctorIso
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))
    (fun i => loopBoundaryKan_kanComplex (r + 1) (F.obj i))
    (boundaryAssemblyOriginalCoherentHomotopy r F) (fun i => by
      rw [boundaryAssemblyOriginalCoherentHomotopy_component]
      exact boundaryKanAssemblyAdjoint_piIsomorphism r (F.obj i))

end SerrePositivity.KST.SConstruction
