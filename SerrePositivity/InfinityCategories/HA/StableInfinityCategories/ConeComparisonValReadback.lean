module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ConeEdgeRebase

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma coneComparison_projected_arrowMk_eq_of_val_eq {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) a b)
    (f : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q)) c d)
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d) (ha : a.val = c.val) (hb : b.val = d.val) :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q)))) := by
  obtain ⟨e', he⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_coneEdge_rebase_of_val_eq e ha hb
  have h : Truncated.HomotopyCategory.homMk e' =
      Truncated.HomotopyCategory.homMk f := hd.isTerminalHo.hom_ext _ _
  have hh := congrArg ((Truncated.mapHomotopyCategory
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q))).map) h
  simp only [Truncated.mapHomotopyCategory_homMk] at hh
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ he.symm).trans
    (congrArg Arrow.mk hh)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
