module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHomotopy

/-!
概要：left fibration のホモトピー圏の射は底で可逆なら可逆。
方針：全辺の左外側ホーン持ち上げと基底の可逆性を使う。
規約：モデル構造の instance を仮定しない。
使われ方：余錐比較の頂点での可逆性から全余錐の可逆性へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SSet.Truncated.HomotopyCategory

/-- 概要：left fibration 上の射は可逆な基底の射の上なら可逆。
方針：代表辺を取り、外側ホーンの相対充填で可逆性を戻す。
規約：元のホモトピー圏の射を保持する。
使われ方：頂点で可逆な指定余錐比較の全可逆性。 -/
lemma leftFibrationHom_isIso_of_map {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {x y : E _⦋0⦌}
    (α : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk y)
    (hα : IsIso ((hoFunctor.map p).toFunctor.map α)) : IsIso α := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y α
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e := by
    intro n σ β _ hw
    have : HasLiftingProperty (horn (n + 2) (0 : Fin (n + 3))).ι p :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro 0 (by change 0 < n + 2; omega))
    let sq : CommSq σ (horn (n + 2) (0 : Fin (n + 3))).ι p β := ⟨hw⟩
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
  exact he.isInvertibleEdge_of_map hα

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
