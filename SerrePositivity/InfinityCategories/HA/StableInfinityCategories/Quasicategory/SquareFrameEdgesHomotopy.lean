module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquareFrameEdges

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

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
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges b t l r) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.squareFrameOfEdges b' t' l' r') := by
  let B := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.fixedEndpointHomotopy b b' hb
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.fixedEndpointHomotopy t t' ht
  let L := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.fixedEndpointHomotopy l l' hl
  let R := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.fixedEndpointHomotopy r r' hr
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

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameEdgesHomotopy := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameEdgesHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameEdgesHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameEdgesHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameEdgesHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameEdgesHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.squareFrameEdgesHomotopy._proof_5
