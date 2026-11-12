module

public import SerrePositivity.KST.Spectra.CofiberMappingPullback
public import SerrePositivity.KST.Spectra.EndpointCircle
public import SerrePositivity.KST.Spectra.PathContractibility

/-!
概要：円からの点つき写像空間と path の終点の基点 fiber の同型。
方針：点つき cofiber の Hom の pullback を終対象と単位 Hom の同型で移す。
規約：実際の単体集合の同型。導来極限の主張ではない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：二端点を潰した円からの Hom は path 終点評価の基点上の pullback。
方針：cofiber の Hom の pullback の二つの下側対象を終対象と標的へ同定する。
規約：標的の基点は Y.basepoint。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の fiber 表示。 -/
theorem endpointCircleMapping_isPullback (Y : PointedSimplicialSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y)
      (terminal.from (PointedObject.basedHom endpointCircle.{u} Y).right)
      (pathEndpoint Y).right (SSet.const (X := ⊤_ SSet.{u}) Y.basepoint) := by
  let T := PointedObject.basedHom (PointedObject.point : PointedSimplicialSet.{u}) Y
  let e₃ : T.right ≅ ⊤_ SSet.{u} := (homPointIsTerminal Y).uniqueUpToIso terminalIsTerminal
  let e₄ := PointedSimplicialSet.forget.mapIso (MonoidalClosed.unitIsoSelf (X := Y))
  have h := cofiberMapping_isPullback _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u} Y
  refine h.of_iso (Iso.refl _) (Iso.refl _) e₃ e₄ ?_ ?_ ?_ ?_
  · simp
  · exact Subsingleton.elim _ _
  · rfl
  · let : IsIso T.hom := isIso_of_isTerminal isTerminalTensorUnit (homPointIsTerminal Y) _
    apply (cancel_epi T.hom).mp
    have hw : T.hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedObject.toPoint (𝟙_ PointedSimplicialSet.{u})) Y ≫ e₄.hom) =
          Y.hom :=
      Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.toPoint (𝟙_ PointedSimplicialSet.{u})) Y ≫
        (MonoidalClosed.unitIsoSelf (X := Y)).hom)
    have hc : SSet.const (X := 𝟙_ SSet.{u}) Y.basepoint = Y.hom := by
      simpa only [toUnit_unit, Category.id_comp] using
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const Y (𝟙_ SSet.{u})).symm
    exact hw.trans (by rw [SSet.comp_const, SSet.comp_const, hc])

/-- 概要：二端点を潰した円からの Hom と path の終点 fiber の同型。
方針：証明済みの pullback の普遍性で選んだ pullback と比較する。
規約：fiber は L9b の実際の KanFiber。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の長完全列。 -/
def endpointCircleFiberIso (Y : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom endpointCircle.{u} Y).right ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (pathEndpoint Y).right Y.basepoint :=
  (endpointCircleMapping_isPullback Y).isoPullback

/-- 概要：円の二端点の商による表示を点つき内部 Hom へ移す。
方針：内部 Hom の反変関手で円の同型を写す。
規約：基点も保存する点つき同型。
使われ方：Goerss–Jardine I §7。loop の fiber 表示の基点の比較。 -/
def loopToEndpointHomIso (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y ≅ PointedObject.basedHom endpointCircle.{u} Y :=
  (MonoidalClosed.internalHom.flip.obj Y).mapIso endpointCircleIso.{u}.op

/-- 概要：loop の単体集合は path の終点評価の基点 fiber と同型。
方針：円の表示の同型と cofiber の Hom の pullback を合成する。
規約：標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の次数移動。 -/
def loopPathFiberIso (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (pathEndpoint Y).right Y.basepoint :=
  PointedSimplicialSet.forget.mapIso (loopToEndpointHomIso Y) ≪≫ endpointCircleFiberIso Y

/-- 概要：loop の fiber 表示を全 path へ含めると点つき射からの制限になる。
方針：pullback の同型の第一射影を計算する。
規約：等式の右辺は点つき射の基礎射。
使われ方：Goerss–Jardine I §7。fiber 表示の基点保存。 -/
@[reassoc]
theorem loopPathFiberIso_hom_ι (Y : PointedSimplicialSet.{u}) :
    (loopPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right Y.basepoint =
      ((loopToEndpointHomIso Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y).right := by
  simp only [loopPathFiberIso, Iso.trans_hom, Category.assoc, endpointCircleFiberIso,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι, IsPullback.isoPullback_hom_fst]
  rfl

/-- 概要：fiber の基点の等式による同型。
方針：基点の等式で型を移す。
規約：全空間と底の射は固定する。
使われ方：Kerodon §3.2.5（Tag 00WD）。path の基点と標的の基点の照合。 -/
def fiberIsoOfEq {E B : SSet.{u}} (p : E ⟶ B) {b b' : B _⦋0⦌} (h : b = b') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b' := eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p) h)

/-- 概要：基点の等式による fiber の同型は包含射と可換。
方針：等式で帰納する。
規約：全空間への包含を変えない。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber の基点の比較。 -/
@[reassoc (attr := simp)]
theorem fiberIsoOfEq_hom_ι {E B : SSet.{u}} (p : E ⟶ B) {b b' : B _⦋0⦌} (h : b = b') :
    (fiberIsoOfEq p h).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b' = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b := by
  subst b'
  exact Category.id_comp _

/-- 概要：定数 path の終点は標的の基点。
方針：終点評価が点つき射であることを使う。
規約：基点は basepoint による頂点表示。
使われ方：Goerss–Jardine I §7。L9b の fiberPoint の基点への照合。 -/
theorem pathEndpoint_basepoint (Y : PointedSimplicialSet.{u}) :
    (pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint = Y.basepoint :=
  congrArg (fun k : 𝟙_ SSet.{u} ⟶ Y.right ↦ k.app _ PUnit.unit) (Under.w (pathEndpoint Y))

/-- 概要：loop を定数 path の像の上の fiber へ同定する。
方針：標的の基点との等式で fiber の基点を移す。
規約：L9b の連結写像と同じ fiber を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。次数移動の同型。 -/
def loopBasedPathFiberIso (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (pathEndpoint Y).right ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) :=
  loopPathFiberIso Y ≪≫ fiberIsoOfEq (pathEndpoint Y).right (pathEndpoint_basepoint Y).symm

/-- 概要：L9b の基点を用いる loop の fiber 同型は全空間への包含と可換。
方針：基点の移送の包含計算と元の fiber 同型の計算を合成する。
規約：右辺は点つき射の基礎射。
使われ方：Kerodon §3.2.5（Tag 00WD）。次数移動の基点保存。 -/
@[reassoc]
theorem loopBasedPathFiberIso_hom_ι (Y : PointedSimplicialSet.{u}) :
    (loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right
      ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint) =
      ((loopToEndpointHomIso Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y).right := by
  rw [loopBasedPathFiberIso, Iso.trans_hom, Category.assoc, fiberIsoOfEq_hom_ι,
    loopPathFiberIso_hom_ι]

/-- 概要：loop の fiber 同型は定数 loop を L9b の fiberPoint へ送る。
方針：全空間への包含後で点つき射の基点保存を検査する。
規約：fiber は定数 path の終点上で取る。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。ホモトピー群の次数移動。 -/
theorem loopBasedPathFiberIso_basepoint (Y : PointedSimplicialSet.{u}) :
    (loopBasedPathFiberIso Y).hom.app _ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (pathEndpoint Y).right (basedPathSpace Y).basepoint := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_ext (pathEndpoint Y).right
    ((pathEndpoint Y).right.app _ (basedPathSpace Y).basepoint)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
  change ((loopBasedPathFiberIso Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (pathEndpoint Y).right _).app _
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint = (basedPathSpace Y).basepoint
  rw [loopBasedPathFiberIso_hom_ι]
  exact congrArg (fun k : 𝟙_ SSet.{u} ⟶ (basedPathSpace Y).right ↦ k.app _ PUnit.unit)
    (Under.w ((loopToEndpointHomIso Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y))

end

end SerrePositivity.KST.Spectra
