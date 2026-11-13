module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointHomTransportBase
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.LeftHomEdgeTransport

/-!
概要：元の全 Hom 輸送の指定点を、元の始点と同じ実際の輸送辺として保持する。
方針：選択済み輸送円柱を指定点で評価し、底の標準区間比較を計算する。
規約：全 Hom の持ち上げを選び直さず、指定した底辺の全一単体を保持する。
使われ方：余錐の全作用の変換を native 単位と元の頂点辺の合成へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  (d : E _⦋0⦌) (y : B _⦋0⦌)

/-- 元の輸送円柱の指定点の同じ辺を、元の始点・輸送先の端点表示で保持する。 -/
def pointHomTransportCylinderEdge
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y) _⦋0⦌) :
    SSet.Edge d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p d y).app (Opposite.op ⦋0⦌) s).val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pointHomTransportCylinder p d y) s).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero d) rfl

/-- 指定底辺の左 Hom の点から取った同じ輸送辺は、元の底辺の全一単体を被覆する。 -/
lemma pointHomTransportCylinderEdge_projection
    (e : SSet.Edge (p.app (Opposite.op ⦋0⦌) d) y) :
    p.app (Opposite.op ⦋1⦌)
      (pointHomTransportCylinderEdge p d y (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e)).edge = e.edge := by
  let s := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e
  have h : (SSet.yonedaEquiv.symm s ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pointHomTransportCylinder p d y).h ≫ p =
        snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pointHomTransportCylinder_base, ← Category.assoc,
      BraidedCategory.braiding_naturality_left, Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, SSet.yonedaEquiv_symm_comp]
    rw [show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftToIntervalMappingSpace (p.app (Opposite.op ⦋0⦌) d) y).app
      (Opposite.op ⦋0⦌) s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e from _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint_interval e]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge_uncurry, ← Category.assoc]
    rfl
  rw [SSet.yonedaEquiv_symm_zero] at h
  have hh := congrArg (fun f => f.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 0)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) h
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  calc
    _ = (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋1⦌)
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := hh
    _ = e.edge := by
      rw [hi]
      change SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge) = _
      rw [Category.id_comp, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
