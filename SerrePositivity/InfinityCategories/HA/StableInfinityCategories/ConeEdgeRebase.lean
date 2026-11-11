module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma exists_coneEdge_rebase_of_val_eq {K X : SSet.{u}}
    {p q : K ⟶ X} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) a b)
    (ha : a.val = c.val) (hb : b.val = d.val) :
    ∃ f : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q)) c d,
      (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection q))).edge =
        (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))).edge := by
  have hpq : p = q := a.property.symm.trans
    ((congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K ≫ v) ha).trans c.property)
  subst q
  have hac : a = c := Subtype.ext ha
  have hbd : b = d := Subtype.ext hb
  subst c
  subst d
  exact ⟨e, rfl⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
