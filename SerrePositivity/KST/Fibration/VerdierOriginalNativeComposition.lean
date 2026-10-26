module
public import SerrePositivity.KST.Fibration.VerdierOriginalNativeHomSquare
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.SquareComposition
public import SerrePositivity.InfinityCategories.Stable.SuspensionSpanComparison
public import SerrePositivity.InfinityCategories.Stable.PastingSplitProjection

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
structure VerdierOriginalNativeComposition (d : VerdierDiagram.{u}) (j k : Fin 2) where
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
    (triangleNativePathIntervalIso.inv ≫ verdierOriginalNativeHomFamily d j)
  top_recovery : top.edge = SSet.yonedaEquiv
    (triangleNativePathIntervalIso.inv ≫ verdierOriginalNativeHomFamily d k)

set_option maxHeartbeats 800000 in
-- 同じ実四角形の四端点輸送と元の三辺を一つの構成データへ束ねる。
/-- 概要：元の二つの全長 Hom を同じ実合成端比較で結ぶ実合成二単体。
方針：元の四角形の四辺を厳密回収し、固定直接端の恒等辺を消去する。
規約：全長 Hom を選び直さず、既存の実三辺の合成判定を消費する。
使われ方：K-6 c4 の有限頂点で指定した合成充填を全族へ戻す。 -/
def verdierOriginalNativeComposition (d : VerdierDiagram.{u}) (j k : Fin 2) :
    VerdierOriginalNativeComposition d j k := by
  let Q := verdierOriginalNativeHomSquare d j k
  let a := (verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ coherentTriangleDirectPath)
  let r := (verdierOriginalCompositeCoreEdgeData d j k).val.toTruncated
  let l : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a a :=
    Truncated.Edge.id (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a
  have hl : (squareLeftArrow Q).edge =
      l.edge := by
    rw [squareLeftArrow_edge, verdierOriginalNativeHomSquare_left]
    exact pinchedConstant_one a
  have hr : (squareRightArrow Q).edge = r.edge := by
    rw [squareRightArrow_edge, verdierOriginalNativeHomSquare_right, Equiv.apply_symm_apply]
    rfl
  have h00 : squareVertex Q 0 0 = a :=
    (squareLeftArrow Q).src_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 1) hl).trans
        l.src_eq)
  have h01 : squareVertex Q 0 1 = a :=
    (squareLeftArrow Q).tgt_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 0) hl).trans
        l.tgt_eq)
  have h10 : squareVertex Q 1 0 = _ :=
    (squareRightArrow Q).src_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 1) hr).trans r.src_eq)
  have h11 : squareVertex Q 1 1 = _ :=
    (squareRightArrow Q).tgt_eq.symm.trans
      ((congrArg ((verdierOriginalNativeHomTarget d).δ 0) hr).trans r.tgt_eq)
  let f : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j))) :=
    ⟨(squareBottomArrow Q).edge, (squareBottomArrow Q).src_eq.trans h00,
      (squareBottomArrow Q).tgt_eq.trans h10⟩
  let g : Truncated.Edge (X := (truncation 2).obj (verdierOriginalNativeHomTarget d)) a
      (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d k))) :=
    ⟨(squareTopArrow Q).edge, (squareTopArrow Q).src_eq.trans h01,
      (squareTopArrow Q).tgt_eq.trans h11⟩
  have hcomp := homMk_comp_eq_of_square f g l r Q rfl rfl hl hr
  have hfac : Truncated.HomotopyCategory.homMk f ≫ Truncated.HomotopyCategory.homMk r =
      Truncated.HomotopyCategory.homMk g := by
    simpa only [l, Truncated.HomotopyCategory.homMk_id, Category.id_comp] using hcomp
  refine ⟨f, g, Classical.choice (compStruct_nonempty_of_homMk_fac hfac), ?_, ?_⟩
  · exact (squareBottomArrow_edge Q).trans
      (congrArg SSet.yonedaEquiv (verdierOriginalNativeHomSquare_bottom d j k))
  · exact (squareTopArrow_edge Q).trans
      (congrArg SSet.yonedaEquiv (verdierOriginalNativeHomSquare_top d j k))

end SerrePositivity.KST.Fibration
