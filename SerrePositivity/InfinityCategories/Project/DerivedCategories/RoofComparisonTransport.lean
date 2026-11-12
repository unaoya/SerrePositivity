module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofFunctorCorrespondence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
/-!
概要：元の実屋根比較の cofinality を、標的の厳密な点・添字表示の変更から独立にする。
方針：標的の全図式を等式で輸送した比較を定義し、等式帰納法で同じ比較へ戻す。
規約：元の実始域と元の分子は変更しない。使われ方：dg の実屋根比較と右 Kan の屋根の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
/-- 指定した標的の厳密な点・添字表示へ輸送した、同じ元の実屋根比較。 -/
def roofComparisonTransport {I X Y : SSet.{u}} (F : X ⟶ Y) (s : I ⟶ X)
    (p : (Δ[0] : SSet.{u}) ⟶ X) (p' : (Δ[0] : SSet.{u}) ⟶ Y) (s' : I ⟶ Y)
    (hp : p ≫ F = p') (hs : s ≫ F = s') :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) s ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p') s' :=
  pullback.lift (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p F ≫
      (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom) (pullback.snd _ _) (by
    rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport hp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, ← Category.assoc, pullback.condition,
      Category.assoc, hs])
/-- 点・添字を後合成のまま表示した、元の実屋根比較。 -/
abbrev rawRoofFunctorMap {I X Y : SSet.{u}} (F : X ⟶ Y) (s : I ⟶ X)
    (p : (Δ[0] : SSet.{u}) ⟶ X) :=
  roofComparisonTransport F s p (p ≫ F) (s ≫ F) rfl rfl
/-- 標的の点・添字の等式輸送は、元の同じ屋根比較の left cofinality を変えない。 -/
lemma roofComparisonTransport_isLeftCofinal_iff {I X Y : SSet.{u}}
    (F : X ⟶ Y) (s : I ⟶ X) (p : (Δ[0] : SSet.{u}) ⟶ X)
    (p' : (Δ[0] : SSet.{u}) ⟶ Y) (s' : I ⟶ Y)
    (hp : p ≫ F = p') (hs : s ≫ F = s') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (roofComparisonTransport F s p p' s' hp hs) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (rawRoofFunctorMap F s p) := by
  subst p' s'
  rfl
/-- 頂点で正規化した元の屋根関手も、同じ raw 屋根比較の cofinality を検査する。 -/
lemma roofFunctorMap_isLeftCofinal_iff_raw {I X Y : SSet.{u}}
    (F : X ⟶ Y) (s : I ⟶ X) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorMap s (s ≫ F) F rfl y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (rawRoofFunctorMap F s (SSet.yonedaEquiv.symm y)) :=
  roofComparisonTransport_isLeftCofinal_iff F s _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetPoint F y) rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
