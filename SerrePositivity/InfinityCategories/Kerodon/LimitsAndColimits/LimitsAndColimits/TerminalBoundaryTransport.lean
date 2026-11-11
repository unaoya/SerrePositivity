module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryIso
public import SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.BoundaryOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary

/-! # 可逆辺による相対終対象の輸送
概要：相対終点境界充填を可逆な辺に沿って移す。
方針：相対始対象の輸送を反転し、二重反転の同型で戻す。
規約：Core の公開 API は変更しない。使われ方：極限錐の輸送。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 概要：反転した射の始点境界充填から終点境界充填を得る。
方針：境界と単体を反転して戻す。
規約：単体集合は任意。使われ方：相対輸送の双対化。 -/
lemma terminalBoundaryLifting_of_initialBoundaryLifting_op {E B : SSet.{u}}
    (p : E ⟶ B) (x : E _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x := by
  intro n a b hfirst sq
  have hlast : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) a =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_vertex, Fin.rev_zero, hfirst, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reverseSimplex_vertex]
  have sq' : CommSq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) a) (boundary (n + 1)).ι
      (SSet.opFunctor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 1) b) := by
    constructor
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_comp, sq.w, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_restrict]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hlast sq'
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 1) F ≫ (SSet.opFunctorCompOpFunctorIso.app E).hom
  refine ⟨G, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_injective E (n + 1)
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hF
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseSimplex_injective B (n + 1)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hFp

/-- 概要：相対終対象を反転すると相対始対象になる。
方針：二重反転の同型と既存の反転補題を使う。
規約：単体集合は任意。使われ方：可逆辺の双対輸送。 -/
lemma TerminalBoundaryLifting.op_initial {E B : SSet.{u}} {p : E ⟶ B} {x : E _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_terminalBoundaryLifting_op
  have h := hx.map_iso (SSet.opFunctorCompOpFunctorIso.app E).symm
    (SSet.opFunctorCompOpFunctorIso.app B).symm (by
      simpa using (SSet.opFunctorCompOpFunctorIso.inv.naturality p).symm)
  exact h

/-- 概要：相対終点境界充填は頂点の同型で保たれる。
方針：同型の逆の辺を反転して相対始対象の輸送を適用する。
規約：quasicategory 間の inner fibration。使われ方：普遍錐の選択の変更。 -/
lemma TerminalBoundaryLifting.of_vertexIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    {x y : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p y := by
  apply terminalBoundaryLifting_of_initialBoundaryLifting_op
  obtain ⟨f, hfm⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective y x e.inv
  have hfi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk f)
    rw [hfm]
    infer_instance
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.IsInvertibleEdge.op hfi
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f
  let a : (Δ[0] : SSet.{u}) ⟶ X.op := SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x)
  have ha : SSet.yonedaEquiv a = (SSet.opObjEquiv.symm x : X.op _⦋0⦌) :=
    SSet.yonedaEquiv.apply_symm_apply _
  let hg : SSet.Truncated.Edge (X := (truncation 2).obj X.op)
      (@SSet.yonedaEquiv X.op ⦋0⦌ a) (SSet.opObjEquiv.symm y) :=
    ⟨g.edge, g.src_eq.trans ha.symm, g.tgt_eq⟩
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge hg := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := hg) (f := g) rfl).2 hf
  exact _root_.SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryLifting.of_invertibleEdge (SSet.opFunctor.map p) a
    (ha.symm ▸ (TerminalBoundaryLifting.op_initial hx)) hg hi

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
