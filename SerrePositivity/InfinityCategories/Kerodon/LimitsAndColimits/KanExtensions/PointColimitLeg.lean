module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IdentityCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalPointAnodyne

/-!
概要：終対象を持つ添字上の余極限余錐の終対象での脚は可逆。
方針：終対象への一点制限で一点図式の余極限へ移し、恒等余錐との比較で脚を評価する。
規約：任意の指定された余錐の脚自身の可逆性を結論する。
使われ方：全部分圏に沿う Kan 拡張の単位の成分の可逆性。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：一点図式の余極限余錐の唯一の脚は可逆。
方針：恒等余錐からの辺は二つの始対象間の同型であり、脚の三角形で元の脚を計算する。
規約：図式 p の表示は任意。
使われ方：終対象で制限した局所 Kan 余錐の脚の可逆性。 -/
lemma kanPointColimit_leg_invertible {D : SSet.{u}} [Quasicategory D]
    {p : (Δ[0] : SSet.{u}) ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (c.leg (𝟙 (Δ[0] : SSet.{u}))) := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  let c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (SSet.yonedaEquiv.symm x) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) c₀ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex x
  let e := Classical.choice (h₀.nonempty_edge c)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := isIso_of_isInitial h₀.isInitialHo hc.isInitialHo _
  have hp := he.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (c₀.leg (𝟙 (Δ[0] : SSet.{u}))) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := SSet.Truncated.Edge.id
      (X := (truncation 2).obj D) x) ?_).2
    · change IsIso (SSet.Truncated.HomotopyCategory.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj D) x))
      rw [SSet.Truncated.HomotopyCategory.homMk_id]
      infer_instance
    · change SSet.yonedaEquiv (_ ≫ SSet.const x) = _
      rw [SSet.comp_const]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (c.leg (𝟙 (Δ[0] : SSet.{u}))))
  rw [← c₀.leg_comp_projection e (𝟙 (Δ[0] : SSet.{u}))]
  exact IsIso.comp_isIso

/-- 概要：終対象を持つ添字上の余極限余錐の終対象での脚は可逆。
方針：終対象の一点包含の right anodyne 性で余極限を制限し、唯一の脚を評価する。
規約：指定された余錐と終対象を選び直さない。
使われ方：包含の像の点における Kan 単位の可逆性。 -/
lemma kanColimit_terminal_leg_invertible {J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (t : J _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (c.leg (SSet.yonedaEquiv.symm t)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointInclusion_mono t
  have hr := hc.restrict_of_rightAnodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne ht)
  have hi := kanPointColimit_leg_invertible (c.restrict (SSet.yonedaEquiv.symm t)) hr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (c.restrict (SSet.yonedaEquiv.symm t)).leg (𝟙 (Δ[0] : SSet.{u}))) ?_).1 hi
  change SSet.yonedaEquiv (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (𝟙 _) ≫ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
