module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitPrismComparisonShape
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitPrismTotalCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLifting

/-!
概要：元の始点余錐と全図式の余錐の制限を結ぶ、余錐圏の区間を構成する。
方針：join と直積の座標を保ち、元の両端と頂点の射を厳密に照合する。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限閉性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の始点余錐から全図式の余錐の制限へ向かう、余錐圏内の区間。 -/
def colimitPrismComparisonSection {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ⟶ X) :
    (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismDiagram G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismComparisonMap K ≫ G) (by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismComparisonMap_inl, Category.assoc]; rfl)

/-- 比較区間の展開は元の prism への形状の射そのもの。 -/
lemma colimitPrismComparisonSection_uncurry {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (colimitPrismComparisonSection G) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismComparisonMap K ≫ G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry _ _

/-- 比較区間の始点は元の始点余錐。 -/
lemma colimitPrismComparisonSection_source {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ⟶ X) :
    stdSimplex.δ (1 : Fin 2) ≫ colimitPrismComparisonSection G =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismEndpoint G 0) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, colimitPrismComparisonSection_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismComparisonMap_source]
  rfl

/-- 比較区間の終点は元の全図式の余錐の制限。 -/
lemma colimitPrismComparisonSection_target {K X : SSet.{u}}
    (G : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ⟶ X) :
    stdSimplex.δ (0 : Fin 2) ≫ colimitPrismComparisonSection G =
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismTotalCocone G).restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, colimitPrismComparisonSection_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismComparisonMap_target]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
