module
public import SerrePositivity.KST.SConstruction.TerminalEndpointCircle
public import SerrePositivity.KST.Spectra.LoopPathFiber

/-! # 元の loop と終点固定 path の始点 fiber
概要：既存の円からの点つき Hom を、終点固定 path の始点評価の fiber と厳密に同定する。
方針：二端点商の Hom の pullback と元の円の同型を合成する。
規約：元の円と区間の商射を保つ。使われ方：元の零行 loop の fiber への包含と π 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open Spectra

/-- 終点基点の二端点商からの Hom は始点評価の基点上の pullback。 -/
lemma terminalEndpointCircleMapping_isPullback (B : PointedSimplicialSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection terminalIntervalStart.{u}) B)
      (terminal.from (PointedObject.basedHom terminalEndpointCircle.{u} B).right)
      (terminalPathStart B).right (SSet.const (X := ⊤_ SSet.{u}) B.basepoint) := by
  let T := PointedObject.basedHom (PointedObject.point : PointedSimplicialSet.{u}) B
  let e₃ : T.right ≅ ⊤_ SSet.{u} := (homPointIsTerminal B).uniqueUpToIso terminalIsTerminal
  let e₄ := PointedSimplicialSet.forget.mapIso (MonoidalClosed.unitIsoSelf (X := B))
  have h := cofiberMapping_isPullback terminalIntervalStart.{u} B
  refine h.of_iso (Iso.refl _) (Iso.refl _) e₃ e₄ ?_ ?_ ?_ ?_
  · simp
  · exact Subsingleton.elim _ _
  · rfl
  · let : IsIso T.hom := isIso_of_isTerminal isTerminalTensorUnit (homPointIsTerminal B) _
    apply (cancel_epi T.hom).mp
    have hw : T.hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.toPoint (𝟙_ PointedSimplicialSet.{u})) B ≫ e₄.hom) =
          B.hom :=
      Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.toPoint
        (𝟙_ PointedSimplicialSet.{u})) B ≫ (MonoidalClosed.unitIsoSelf (X := B)).hom)
    have hc : SSet.const (X := 𝟙_ SSet.{u}) B.basepoint = B.hom := by
      simpa only [toUnit_unit, Category.id_comp] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const B (𝟙_ SSet.{u})).symm
    exact hw.trans (by rw [SSet.comp_const, SSet.comp_const, hc])

/-- 二端点商からの Hom と始点評価の元の Kan fiber の同型。 -/
def terminalEndpointCircleFiberIso (B : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom terminalEndpointCircle.{u} B).right ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (terminalPathStart B).right B.basepoint :=
  (terminalEndpointCircleMapping_isPullback B).isoPullback

/-- 元の円の表示の同型を点つき内部 Hom へ移す。 -/
def loopToTerminalEndpointHomIso (B : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B ≅ PointedObject.basedHom terminalEndpointCircle.{u} B :=
  (MonoidalClosed.internalHom.flip.obj B).mapIso terminalEndpointCircleIso.{u}.op

/-- 元の loop の単体集合と終点固定 path の始点 fiber の同型。 -/
def loopTerminalPathFiberIso (B : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (terminalPathStart B).right B.basepoint :=
  PointedSimplicialSet.forget.mapIso (loopToTerminalEndpointHomIso B) ≪≫
    terminalEndpointCircleFiberIso B

/-- 同型を path 空間へ含めると元の二端点商射による制限になる。 -/
lemma loopTerminalPathFiberIso_hom_ι (B : PointedSimplicialSet.{u}) :
    (loopTerminalPathFiberIso B).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (terminalPathStart B).right B.basepoint =
      ((loopToTerminalEndpointHomIso B).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
          (pointedCofiberProjection terminalIntervalStart.{u}) B).right := by
  simp only [loopTerminalPathFiberIso, Iso.trans_hom, Category.assoc,
    terminalEndpointCircleFiberIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι, IsPullback.isoPullback_hom_fst]
  rfl

/-- 終点固定 path の始点評価は定数 path の基点を標的の基点へ送る。 -/
lemma terminalPathStart_basepoint (B : PointedSimplicialSet.{u}) :
    (terminalPathStart B).right.app _ (terminalPathSpace B).basepoint = B.basepoint :=
  congrArg (fun k : 𝟙_ SSet.{u} ⟶ B.right => k.app _ PUnit.unit) (Under.w (terminalPathStart B))

/-- fiber の基点を定数 path の実際の像で表した元の loop の同型。 -/
def loopTerminalBasedPathFiberIso (B : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (terminalPathStart B).right
      ((terminalPathStart B).right.app _ (terminalPathSpace B).basepoint) :=
  loopTerminalPathFiberIso B ≪≫
    fiberIsoOfEq (terminalPathStart B).right (terminalPathStart_basepoint B).symm

/-- 基点の等式で移した後も元の path 空間への包含と可換。 -/
lemma loopTerminalBasedPathFiberIso_hom_ι (B : PointedSimplicialSet.{u}) :
    (loopTerminalBasedPathFiberIso B).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (terminalPathStart B).right
      ((terminalPathStart B).right.app _ (terminalPathSpace B).basepoint) =
      ((loopToTerminalEndpointHomIso B).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
          (pointedCofiberProjection terminalIntervalStart.{u}) B).right := by
  rw [loopTerminalBasedPathFiberIso, Iso.trans_hom, Category.assoc,
    fiberIsoOfEq_hom_ι, loopTerminalPathFiberIso_hom_ι]

/-- 元の loop と始点 fiber の同型は定数 loop を定数 path 上の基点へ送る。 -/
lemma loopTerminalBasedPathFiberIso_basepoint (B : PointedSimplicialSet.{u}) :
    (loopTerminalBasedPathFiberIso B).hom.app _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).basepoint =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (terminalPathStart B).right (terminalPathSpace B).basepoint := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_ext (terminalPathStart B).right
    ((terminalPathStart B).right.app _ (terminalPathSpace B).basepoint)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
  change ((loopTerminalBasedPathFiberIso B).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (terminalPathStart B).right _).app _
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).basepoint = (terminalPathSpace B).basepoint
  rw [loopTerminalBasedPathFiberIso_hom_ι]
  exact congrArg (fun k : 𝟙_ SSet.{u} ⟶ (terminalPathSpace B).right => k.app _ PUnit.unit)
    (Under.w ((loopToTerminalEndpointHomIso B).hom ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection terminalIntervalStart.{u}) B))

end SerrePositivity.KST.SConstruction
