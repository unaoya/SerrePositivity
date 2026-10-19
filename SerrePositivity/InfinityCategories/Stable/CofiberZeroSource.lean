module
public import SerrePositivity.InfinityCategories.Stable.ZeroCofiberIso
public import SerrePositivity.InfinityCategories.Stable.SuspensionSquare

/-! # 零始点の辺の実 cofiber 対象

概要：零始点から対象への任意の辺の cofiber はその対象と実同型。
方針：指定した底辺から二頂点を回収し、押し出しの右辺を同型と判定する。
規約：安定性は不要。使われ方：辺の反転条件から対象の零化を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} {x y : X _⦋0⦌}
variable {f : Truncated.Edge (X := (truncation 2).obj X) x y}

/-- cofiber 四角形の始点は指定した実辺の始点。 -/
lemma CofiberSquare.source_vertex (s : CofiberSquare f) : squareVertex s.square 0 0 = x := by
  exact (squareBottomEdge_source s.square).symm.trans
    ((congrArg (fun q => X.δ 1 (SSet.yonedaEquiv q)) s.bottom_edge).trans
      ((congrArg (X.δ 1) (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.src_eq))

/-- cofiber 四角形の底辺の終点は指定した実辺の終点。 -/
lemma CofiberSquare.target_vertex (s : CofiberSquare f) : squareVertex s.square 1 0 = y := by
  exact (squareBottomEdge_target s.square).symm.trans
    ((congrArg (fun q => X.δ 0 (SSet.yonedaEquiv q)) s.bottom_edge).trans
      ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.tgt_eq))

/-- 零始点の辺の cofiber はその実終点と同型。 -/
def CofiberSquare.cofiberIsoOfZeroSource [Quasicategory X]
    (s : CofiberSquare f) (hx : IsZeroVertex x) : VertexIso s.cofiber y := by
  have hi : IsIso (squareHoRight s.square) :=
    isIso_squareHoRight_of_pushout_initial_left s.square s.isPushout
      (by rw [s.source_vertex]; exact hx.1) s.zero_corner.1
  let e : VertexIso (squareVertex s.square 1 0) s.cofiber := asIso (squareHoRight s.square)
  exact e.symm ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk s.target_vertex)

end SerrePositivity.InfinityCategories
