module
public import SerrePositivity.KST.SConstruction.PointedKanHomotopyComponents

/-! # 元の点つき成分の π 同型から図式全体の同型を検出する
概要：全入力単体を持つ変換の回収成分が π_* 同型なら、変換そのものが関手同型。
方針：同じ成分の coherent な辺の可逆性を、関手空間の点ごとの判定に渡す。
規約：別の同型の存在から指定した変換の可逆性を推測しない。
使われ方：既存の Ω 条件を元の模型の coherent な図式へ移す。
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

/-- 回収した元の成分が全基点 π 同型なら、指定した全体変換が関手同型。 -/
def pointedKanDiagramHomotopyFunctorIso {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (H : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (hH : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedKanDiagramHomotopyMapAt hF hG H i).right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy H
  rintro ⟨s⟩
  have hs : s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (s.obj 0) := ComposableArrows.ext₀ rfl
  rw [hs]
  let f : (pointedKanDiagram F hF).obj (s.obj 0) ⟶ (pointedKanDiagram G hG).obj (s.obj 0) :=
    ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hG H (s.obj 0))
  have hf := pointedKanObject_edge_isInvertible_of_piIsomorphism f (hH (s.obj 0))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (pointedKanDiagramHomotopyMapAt_edge hF hG H (s.obj 0))).mp hf

end SerrePositivity.KST.SConstruction
