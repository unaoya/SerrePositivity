module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FixedCoconeBoundaryUnderInclusion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：三条件を固定した余錐の族を、同じ条件を保つ実際の全写像へ展開する。
方針：二つの実 fiber の包含を uncurry し、三つの定値射影を全写像の式へ戻す。
規約：パラメーターの充填性を仮定しない。
使われ方：指定始点評価を固定した比較の実可逆円柱への表示。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {A X Z Q : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)
  (e : X ⟶ Z) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ Z)
  (m : Q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedCoconeBoundaryUnder p b e s)

/-- 概要：三条件固定の余錐族の実際の全写像。方針：同じ包含を uncurry する。
規約：全係数を保持。使われ方：実可逆円柱。 -/
def fixedCoconeBoundaryUnderFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⊗ Q ⟶ X :=
  uncurry (m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedCoconeBoundaryUnderInclusion p b e s)

/-- 概要：実全写像の底図式は全時刻で固定。方針：定値射影を uncurry する。
規約：全係数を保持。使われ方：相対反映の底境界。 -/
lemma fixedCoconeBoundaryUnderFamily_old :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}) ▷ Q) ≫ fixedCoconeBoundaryUnderFamily p b e s m =
      fst A Q ≫ b := by
  rw [fixedCoconeBoundaryUnderFamily, ← uncurry_pre_app, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedCoconeBoundaryUnderInclusion_old, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：実全写像の終点図式は全時刻で固定。方針：定値射影を uncurry する。
規約：全係数を保持。使われ方：相対反映の終点境界。 -/
lemma fixedCoconeBoundaryUnderFamily_tip :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u}) ▷ Q) ≫ fixedCoconeBoundaryUnderFamily p b e s m =
      fst (Δ[0] : SSet.{u}) Q ≫ p := by
  rw [fixedCoconeBoundaryUnderFamily, ← uncurry_pre_app, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedCoconeBoundaryUnderInclusion_tip, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：実全写像の指定評価も全時刻で固定。方針：定値射影を uncurry する。
規約：全係数を保持。使われ方：指定始点下の相対反映。 -/
lemma fixedCoconeBoundaryUnderFamily_evaluation :
    fixedCoconeBoundaryUnderFamily p b e s m ≫ e = fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) Q ≫ s := by
  rw [fixedCoconeBoundaryUnderFamily, ← uncurry_natural_right, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedCoconeBoundaryUnderInclusion_evaluation, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
