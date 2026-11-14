module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSpanColimitTransfer
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PushoutCommonExtension

/-!
概要：指定した部分余極限を、任意の図式に共通拡張として付加する。
方針：元の図式と部分余錐を pushout の普遍性で貼り、coslice 制限を使う。
規約：部分図式の射に単射性は要求せず、元の図式を厳密に保つ。
使われ方：二つの図式に同じ部分余極限頂点を付加してから貼り合わせる。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {A B X : SSet.{u}} {p : A ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (f : A ⟶ B) (F : B ⟶ X) (hf : f ≫ F = p)

/-- 図式に同じ部分余極限全余錐を付加した実図式。 -/
def commonColimitDiagram : pushout f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ⟶ X :=
  pushout.desc F c.val (hf.trans c.property.symm)

/-- 元の図式をそのまま回収する。 -/
lemma commonColimitDiagram_base :
    pushout.inl f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ≫ commonColimitDiagram c f F hf = F :=
  pushout.inl_desc _ _ _

/-- 指定された部分余極限の全余錐をそのまま回収する。 -/
lemma commonColimitDiagram_cone :
    pushout.inr f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ≫ commonColimitDiagram c f F hf = c.val :=
  pushout.inr_desc _ _ _

/-- 部分余極限の付加は、その元の図式の余極限存在を保ち反映する。 -/
lemma hasColimit_commonColimitDiagram_iff [Quasicategory X] (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (commonColimitDiagram c f F hf) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceRestriction_trivialKanFibration_of_colimit_attachment c hc f
    (pushout.inr f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0])) (pushout.inl f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]))
    (IsPushout.of_hasPushout f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0])).flip
    (commonColimitDiagram c f F hf) (commonColimitDiagram_cone c f F hf)
  simpa only [commonColimitDiagram_base] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction (commonColimitDiagram c f F hf)
      (pushout.inl f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
