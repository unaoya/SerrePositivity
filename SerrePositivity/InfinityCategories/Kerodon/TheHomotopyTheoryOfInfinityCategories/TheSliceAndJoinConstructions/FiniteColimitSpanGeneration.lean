module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FiniteColimitGeneration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.PointConeSpanIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EmptyShapeExistence

/-!
概要：始対象と標準 span の余極限から、全有限余極限を生成する。
方針：空形状基底と三頂点 span の同型を、有限セル帰納へ渡す。
規約：押し出しは元の標準ホーン全図式の native な余極限として量化する。
使われ方：Ind と一般の quasicategory の有限余極限存在の公開判定。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 始対象と全押し出しが存在すれば、全有限単体集合形状の余極限が存在する。 -/
lemma hasFiniteColimits_of_initial_pushouts {X : SSet.{u}} [Quasicategory X]
    (t : X _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex t)
    (hs : ∀ p : (horn 2 0 : SSet.{u}) ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_empty_pointSpan
    (fun T p => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasColimit_emptyDiagram_of_initial p t ht)
  intro p
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_restrict_of_isIso p _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpanIso.inv).mpr (hs _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.2.4" (partial := direction) "仮定：準圏に始対象とすべての span の余極限が存在する（HTT の十分方向と一致）。結論：任意の有限単体集合形状の図式に余極限が存在する（一致する方向。逆向きは同じ宣言に含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_initial_pushouts
attribute [cite HTT "4.4.2.6" (partial := special) "仮定：小余積と押し出しが存在する（Lean が強い：任意の正則濃度の切断ではなく固定宇宙内の全小余積。空余積と押し出しから有限余極限を得て恒等関手に適用）。結論：同じ元の小図式に余極限が存在する（一致する場合。任意の κ による切断は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasFiniteColimits_of_initial_pushouts
