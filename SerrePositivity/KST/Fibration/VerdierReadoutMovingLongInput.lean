module
public import SerrePositivity.KST.Fibration.VerdierReadoutCompositionBoundary
public import SerrePositivity.KST.Fibration.VerdierMovingUpperComposite

/-!
概要：同じ実下側読出しと全 S• 比較の相対合成を、動く上側の実長 Hom 入力へ渡す。
方針：同じ合成の全 path 端を元の二短辺の豊穣合成へ厳密に照合する。
規約：長 Hom 入力の存在を仮定せず、同じ実相対合成から構成する。
使われ方：K-6 c4 の元の下側共有対角を持つ動く実上側族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
    (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
  (hL : VerdierLowerNativeReadoutRecovery d L)
  (hfull : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d Δ[1])

variable
  (H : SSet.Homotopy
    ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))
    (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (verdierNativeCompositePoint d 1)))
  (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (verdierReadoutUpperComparison d)
    (verdierLowerNativeReadoutHomotopy d L hL) H)
  (hT : T.diagram ≫ (pre verdierReadoutPathBoundary.{u}).app _ =
    curry (verdierReadoutBoundaryDiagram d L hL hfull))
include hT


/-- 概要：同じ相対合成の全 path 端は、動く実二短辺の全豊穣合成。
方針：同じ境界回収式へ元の全 S• 成分照合を代入する。
規約：全時刻の厳密等式。使われ方：実長 Hom fiber への登録。 -/
theorem verdierReadoutComposition_movingComposite :
    curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierMovingUpperCompositeFamily d := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex,
    verdierReadoutComposition_full d L hL hfull H T hT,
    verdierMovingUpperCompositeFamily_component]

/-- 概要：同じ相対合成から元の動く二短辺に整合する実長 Hom 入力を構成する。
方針：全合成端回収を元の fiber 頂点構成子へ渡す。
規約：追加の存在仮定や長 Hom の再選択を行わない。
使われ方：元の実上側 canonical encoder への入力。 -/
def verdierReadoutMovingLongInput : (verdierMovingUpperLongSpace d) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomVertex
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) Δ[1]
    (verdierMovingUpperCompositeFamily d) (curry H.h)
    (verdierReadoutComposition_movingComposite d L hL hfull H T hT)

/-- 概要：同じ実入力の全長 Hom は元の相対合成そのもの。
方針：同じ fiber 頂点の実全族回収を使う。
規約：元の同じ合成を保持。使われ方：直接端と有限端点の同時回収。 -/
theorem verdierReadoutMovingLongInput_value :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue (verdierReadoutMovingLongInput d L hL hfull H T hT) =
      curry H.h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomVertex_value _ _ _ _ _ _

/-- 概要：同じ実上側入力の直接端は元の同じ下側読出しの直接端全族。
方針：相対合成の指定直接端を同じ下側ホモトピーの uncurry 回収へ戻す。
規約：非退化一単体を含む全時刻の厳密等式。
使われ方：正規化した下側との全共有対角の貼り合わせ。 -/
theorem verdierReadoutMovingLongInput_direct :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue (verdierReadoutMovingLongInput d L hL hfull H T hT) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})) =
    verdierLowerNativeLongHomTransport d Δ[1] L ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath.{u})) := by
  rw [verdierReadoutMovingLongInput_value, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex,
    verdierReadoutComposition_direct d L hL hfull H T hT,
    verdierReadoutComponentCurve, verdierLowerNativeReadoutHomotopy_h,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, curry_uncurry]

end SerrePositivity.KST.Fibration
