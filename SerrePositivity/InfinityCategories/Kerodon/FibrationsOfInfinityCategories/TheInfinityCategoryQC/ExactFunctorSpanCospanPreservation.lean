module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SquareConePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor

/-!
概要：安定圏間の完全関手は実際の span 余極限と cospan 極限を保つ。
方針：元の全錐を四角形へ直し、完全関手の四角形保存を使って元へ戻す。
規約：元の指定図式と全錐の射を保持する。
使われ方：lax pullback の存在・成分判定の保存仮定を完全性から導く。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]

/-- 概要：完全関手は指定した cospan 極限錐を保つ。
方針：元の錐の引き戻し四角形を保存し、全錐の射の等式で極限性を戻す。
規約：cospan 図式の極限の存在はこの補題では仮定しない。
使われ方：lax pullback の fiber 側の保存条件。 -/
lemma exactFunctor_preserves_cospan_limit (f : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f]
    {r : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone r) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone f c) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPullbackSquare f (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback c hc)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c ≫ f)) ?_).2 h
  change c.val ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ c.val) ≫ f)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 概要：完全関手は指定した span 余極限余錐を保つ。
方針：元の余錐の押し出し四角形を保存し、全余錐の射の等式で戻す。
規約：任意の指定余錐の普遍性を保つ。
使われ方：lax pullback の cofiber 側の保存条件。 -/
lemma exactFunctor_preserves_span_colimit (f : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f]
    {r : (horn 2 0 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone f c) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare f (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout c hc)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c ≫ f)) ?_).2 h
  change c.val ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.inv ≫ c.val) ≫ f)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
