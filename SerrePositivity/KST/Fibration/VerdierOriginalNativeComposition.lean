module
public import SerrePositivity.KST.Fibration.VerdierOriginalNativeHomSquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareComposition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSpanComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingSplitProjection

/-!
概要：元の上下全長 Hom と同じ実合成端比較を三辺に持つ実合成二単体を構成する。
方針：元の実比較四角形の固定直接端を消去し、既存の合成二単体判定を使う。
規約：元の上下 path と合成端比較を保持し、新しい存在仮定を取らない。
使われ方：K-6 c4 の有限入力点で全長 Hom を指定する充填条件。
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

/-- 概要：元の上下 path と実合成端比較を厳密保持する合成二単体のデータ。
方針：直接端を共通始点とし、指定二辺とその実合成を記録する。
規約：同型類だけでなく元の実一単体を保持する。
使われ方：有限入力点で指定する長 Hom の二単体。 -/
structure VerdierOriginalNativeComposition (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) where
  bottom : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d))
    ((verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleDirectPath))
    (SimplicialCategory.homEquiv' _ _
      (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j)))
  top : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d))
    ((verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleDirectPath))
    (SimplicialCategory.homEquiv' _ _
      (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d k)))
  triangle : Truncated.Edge.CompStruct bottom
    (verdierOriginalCompositeCoreEdgeData d j k).val.toTruncated top
  bottom_recovery : bottom.edge = SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv ≫ verdierOriginalNativeHomFamily d j)
  top_recovery : top.edge = SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv ≫ verdierOriginalNativeHomFamily d k)

set_option maxHeartbeats 800000 in
-- 同じ実四角形の四端点輸送と元の三辺を一つの構成データへ束ねる。
/-- 概要：元の二つの全長 Hom を同じ実合成端比較で結ぶ実合成二単体。
方針：元の四角形の四辺を厳密回収し、固定直接端の恒等辺を消去する。
規約：全長 Hom を選び直さず、既存の実三辺の合成判定を消費する。
使われ方：K-6 c4 の有限頂点で指定した合成充填を全族へ戻す。 -/
def verdierOriginalNativeComposition (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    VerdierOriginalNativeComposition d j k := by
  let Q := verdierOriginalNativeHomSquare d j k
  let a := (verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ coherentTriangleDirectPath)
  let r := (verdierOriginalCompositeCoreEdgeData d j k).val.toTruncated
  let l : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a a :=
    Truncated.Edge.id (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a
  have hl : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q).edge =
      l.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge, verdierOriginalNativeHomSquare_left]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one a
  have hr : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow Q).edge = r.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, verdierOriginalNativeHomSquare_right, Equiv.apply_symm_apply]
    rfl
  have h00 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 0 = a :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q).src_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 1) hl).trans
        l.src_eq)
  have h01 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1 = a :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q).tgt_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 0) hl).trans
        l.tgt_eq)
  have h10 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 1 0 = _ :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow Q).src_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 1) hr).trans r.src_eq)
  have h11 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 1 1 = _ :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow Q).tgt_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 0) hr).trans r.tgt_eq)
  let f : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j))) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow Q).edge, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow Q).src_eq.trans h00,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow Q).tgt_eq.trans h10⟩
  let g : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d k))) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow Q).edge, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow Q).src_eq.trans h01,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow Q).tgt_eq.trans h11⟩
  have hcomp := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square f g l r Q rfl rfl hl hr
  have hfac : Truncated.HomotopyCategory.homMk f ≫ Truncated.HomotopyCategory.homMk r =
      Truncated.HomotopyCategory.homMk g := by
    simpa only [l, Truncated.HomotopyCategory.homMk_id, Category.id_comp] using hcomp
  refine ⟨f, g, Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hfac), ?_, ?_⟩
  · exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge Q).trans
      (congrArg SSet.yonedaEquiv (verdierOriginalNativeHomSquare_bottom d j k))
  · exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge Q).trans
      (congrArg SSet.yonedaEquiv (verdierOriginalNativeHomSquare_top d j k))

end SerrePositivity.KST.Fibration
