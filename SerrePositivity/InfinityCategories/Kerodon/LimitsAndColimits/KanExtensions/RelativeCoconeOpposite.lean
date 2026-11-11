module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeTerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CosliceOpposite

/-!
概要：標準相対余極限余錐の反転は標準相対極限錐と同値。
方針：coslice の反転同型の後合成自然性と相対頂点条件の双対性を合成する。
規約：余錐全体の指定代表を反転する。
使われ方：左右 Kan の標準局所相対条件の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：通常の coslice の反転同型は標的への後合成に自然。
方針：反転後の錐の値を計算し、反転関手の合成則で比較する。
規約：全次数の射の等式として述べる。
使われ方：相対余極限を反転した相対極限へ移す可換正方形。 -/
lemma kanSliceUnderOpIso_postcomp {K D E : SSet.{u}} (p : K ⟶ D) (U : D ⟶ E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso p).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.opFunctor.map p) (SSet.opFunctor.map U) =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso (p ≫ U)).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpObjEquiv p n.unop s).val ≫ SSet.opFunctor.map U =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpObjEquiv (p ≫ U) n.unop
      ((SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U)).app n s)).val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpObjEquiv_val, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpObjEquiv_val]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso n.unop).inv (𝟙 K.op) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K (stdSimplex.obj n.unop)).inv ≫
      SSet.opFunctor.map (SSet.opObjEquiv s).val) ≫ SSet.opFunctor.map U =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso n.unop).inv (𝟙 K.op) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K (stdSimplex.obj n.unop)).inv ≫
        SSet.opFunctor.map ((SSet.opObjEquiv s).val ≫ U)
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- 概要：標準相対余極限余錐は反転した標準相対極限錐と同値。
方針：相対始対象を相対終対象へ反転し、coslice の反転同型で slice へ移す。
規約：添字の充填性や U の inner 性は不要。
使われ方：元の左右 Kan 関手の標準相対条件の双対化。 -/
lemma kanIsRelativeColimitCone_iff_reverseCone {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) {p : K ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone (SSet.opFunctor.map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInitialVertex_iff_terminal_op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U) c).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeTerminalVertex_iff_of_iso_square
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.opFunctor.map p) (SSet.opFunctor.map U))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderOpIso (p ≫ U))
      (kanSliceUnderOpIso_postcomp p U) (SSet.opObjEquiv.symm c))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
