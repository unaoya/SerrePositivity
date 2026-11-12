module
public import SerrePositivity.KST.SConstruction.PointedKanHomotopyComponents
public import SerrePositivity.KST.SConstruction.PointedKanHomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-! # 図式全体の合成三角形を元の点つき成分へ戻す
概要：全入力単体で指定した三つの変換の合成を、元の Kan 模型の成分で回収する。
方針：関手空間の二単体を各対象で評価し、coherent nerve の三角形を忠実に反映する。
規約：三辺の代表は全体の変換から取り出した同じ一単体。
使われ方：比較逆射・Kan 延長の全体構成と既存の選択構造射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全体の円柱を curry して対象で評価すると、元の対象成分の辺を回収する。 -/
lemma pointedKanDiagramHomotopyMapAt_yoneda {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (H : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (i : I) :
    SSet.yonedaEquiv (curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (pointedKanDiagram F hF).obj i ⟶
        (pointedKanDiagram G hG).obj i from
          ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hG H i))).edge := by
  rw [pointedKanDiagramHomotopyMapAt_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  change H.h.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u+1}))) = _
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u+1})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]
  rfl

/-- 関手空間の指定三辺の実三角形は、回収した元の点つき成分の合成を証明する。 -/
lemma pointedKanDiagramTriangle_components {I : Type u} [SmallCategory I]
    {F G J : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (hJ : ∀ i, KanComplex (J.obj i).right)
    (l : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (r : SSet.Homotopy (pointedKanCoherentDiagram G hG) (pointedKanCoherentDiagram J hJ))
    (d : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram J hJ))
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) (i : I) :
    componentOf (pointedKanDiagramHomotopyMapAt hF hG l i ≫
      pointedKanDiagramHomotopyMapAt hG hJ r i) =
      componentOf (pointedKanDiagramHomotopyMapAt hF hJ d i) := by
  let a : (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i :=
    ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hG l i)
  let b : (pointedKanDiagram G hG).obj i ⟶ (pointedKanDiagram J hJ).obj i :=
    ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hG hJ r i)
  let c : (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram J hJ).obj i :=
    ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hJ d i)
  apply pointedKanObject_component_comp_of_triangle a b c
  refine SSet.Edge.CompStruct.mk
    (SSet.yonedaEquiv (T.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))) ?_ ?_ ?_
  · rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_two]
    exact pointedKanDiagramHomotopyMapAt_yoneda hF hG l i
  · rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_zero]
    exact pointedKanDiagramHomotopyMapAt_yoneda hG hJ r i
  · rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, T.face_one]
    exact pointedKanDiagramHomotopyMapAt_yoneda hF hJ d i

end SerrePositivity.KST.SConstruction
