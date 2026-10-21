module

public import SerrePositivity.KST.LocalizingInvariants.SquareFrameEdges

/-!
概要：端点を共有する四辺の同じホモトピー類から、角を厳密に保つ境界変形を作る。
方針：四辺の各端点に同じ恒等 path を指定する。
規約：正方形本体の比較は境界延長で行う。使われ方：元の BF 二脚を持つ正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def squareFrameEdgesHomotopy {X : SSet.{u}} [Quasicategory X] {x y x' z : X _⦋0⦌}
    (b b' : X.Edge x y) (t t' : X.Edge x' z) (l l' : X.Edge x x') (r r' : X.Edge y z)
    (hb : Truncated.HomotopyCategory.homMk b.toTruncated =
      Truncated.HomotopyCategory.homMk b'.toTruncated)
    (ht : Truncated.HomotopyCategory.homMk t.toTruncated =
      Truncated.HomotopyCategory.homMk t'.toTruncated)
    (hl : Truncated.HomotopyCategory.homMk l.toTruncated =
      Truncated.HomotopyCategory.homMk l'.toTruncated)
    (hr : Truncated.HomotopyCategory.homMk r.toTruncated =
      Truncated.HomotopyCategory.homMk r'.toTruncated) :
    SquareFrameHomotopy (squareFrameOfEdges b t l r) (squareFrameOfEdges b' t' l' r') := by
  let B := fixedEndpointHomotopy b b' hb
  let T := fixedEndpointHomotopy t t' ht
  let L := fixedEndpointHomotopy l l' hl
  let R := fixedEndpointHomotopy r r' hr
  exact {
    bottom := B.homotopy
    top := T.homotopy
    left := L.homotopy
    right := R.homotopy
    lower_left := B.source.trans L.source.symm
    lower_right := B.target.trans R.source.symm
    upper_left := T.source.trans L.target.symm
    upper_right := T.target.trans R.target.symm
    bottom_invertible := B.invertible
    top_invertible := T.invertible
    left_invertible := L.invertible
    right_invertible := R.invertible }

end SerrePositivity.KST.LocalizingInvariants
