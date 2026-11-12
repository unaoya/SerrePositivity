module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictNativeCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BNerveComparisonCoconeLeg

/-!
概要：小さい終頂点付加余錐の宇宙移送は、元の指定脚を保つ。
方針：join の一次単体の座標で宇宙同型を評価する。
規約：同じ全一次単体の等式を公開する。
使われ方：拡張ホモロジー余錐と native 余錐の脚の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory SSet
open scoped _root_.Simplicial

lemma dgBarJoinIntervalIdentity :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) := by
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).app (Opposite.op ⦋1⦌)).toEquiv.injective
  simp only [CategoryTheory.Iso.toEquiv_fun]
  erw [← SSet.yonedaEquiv_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 0 0).hom, Iso.inv_hom_id]
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma dgBarJoinCoconeLeg_yoneda {K : SSet.{u}} (x : K _⦋0⦌) :
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm x) (𝟙 (Δ[0] : SSet.{u}))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex x := by
  rw [SSet.yonedaEquiv_comp, dgBarJoinIntervalIdentity,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex_natural, SSet.yonedaEquiv_symm_app_id]

lemma dgBarUliftCoconeLegShape (K : SSet.{u}) (x : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso.{u, v} K 0).inv.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (ULift.up x)) =
        ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex x) := by
  rfl

lemma dgBarCoconeUlift_leg {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (x : K _⦋0⦌) :
    (c.ulift.{u, v}).val.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (ULift.up x)) =
        ULift.up (c.val.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex x)) := by
  change ((SSet.uliftFunctor.{v, u}).map c.val).app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso K 0).inv.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (ULift.up x))) = _
  rw [dgBarUliftCoconeLegShape]
  rfl

lemma dgBarTerminalNativeCocone_leg (R : Type u) (D : Type v)
    {J : Type u} [Category.{u} J] (j : J) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone R D (J := J)).val.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (ULift.up (nerveEquiv.symm j))) =
        ULift.up (ComposableArrows.mk₁ (WithTerminal.homFrom j)) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarTerminalNativeCocone, dgBarCoconeUlift_leg]
  exact congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_leg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.withTerminalCocone J) j)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
