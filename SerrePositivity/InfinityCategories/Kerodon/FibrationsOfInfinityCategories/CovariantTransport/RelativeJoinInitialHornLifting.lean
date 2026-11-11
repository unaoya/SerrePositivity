module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinInitialHornLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection

/-!
概要：切断一の相対 join の外ホーン充填を係数側の充填へ還元する。
方針：時間と係数の充填を区間付き対角へ写し、通常の join の持ち上げを引き戻す。
規約：右因子の構造射は恒等射。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、標準 prism の垂直辺の cocartesian 性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：時間の切断が一で係数側に充填があれば相対 join の外ホーンを持ち上げられる。
方針：係数の充填と時間を対にし、joinMap の外ホーン持ち上げを pullback の射にする。
規約：X と Y の quasicategory 性は要求せず、係数側の充填を明示的に入力する。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、恒等係数辺に沿う外ホーンの充填。 -/
lemma relativeJoin_initialHorn_hasLift_of_coefficient {X Y : SSet.{u}} (n : ℕ)
    (f : X ⟶ Y) (a : (horn (n + 2) 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y))
    (b : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (sq : CommSq a (horn (n + 2) 0).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y)) b)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv b)).toOrderHom 1 = 1)
    (c : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hc : (horn (n + 2) 0).ι ≫ c = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 Y)) :
    sq.HasLift := by
  let τ : (Δ[n + 2] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ Y := lift b c
  have hτ : (horn (n + 2) 0).ι ≫ τ =
      a ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      exact sq.w.symm
    · rw [Category.assoc, lift_snd]
      exact hc
  let β := τ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y
  have hβ : (horn (n + 2) 0).ι ≫ β =
      (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) := by
    change ((horn (n + 2) 0).ι ≫ τ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y = _
    rw [hτ, Category.assoc, ← pullback.condition, ← Category.assoc]
  have hβcut : (SSet.yonedaEquiv β).1.val = 1 := by
    rw [SSet.yonedaEquiv_comp]
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y).app (Opposite.op ⦋n + 2⦌)
      (SSet.yonedaEquiv b, SSet.yonedaEquiv c)).1.val = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_app_cut]
    exact hb
  obtain ⟨d, hd, hdβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinMap_right_id_initialHorn_hasLift_of_cut_one n f
    (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)) β hβ hβcut
  let l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) :=
    pullback.lift d τ hdβ
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact hd
    · rw [Category.assoc, pullback.lift_snd]
      exact hτ
  · change (pullback.lift d τ hdβ ≫ pullback.snd _ _) ≫ fst Δ[1] Y = b
    rw [pullback.lift_snd]
    exact lift_fst b c

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
