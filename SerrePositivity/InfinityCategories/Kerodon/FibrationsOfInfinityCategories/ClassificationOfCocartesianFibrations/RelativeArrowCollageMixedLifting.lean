module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeArrowCollage
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinMixedLeftHornLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：底上の相対射の区間実現に対する混合した左ホーンの持ち上げ。
方針：終域の left fibration で係数を充填し joinMap の混合持ち上げへ戻す。
規約：始域の left fibration 性は混合分岐には不要。
使われ方：全ての時間の切断を合わせて区間実現の left fibration 性を得る。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：混合した左ホーンの relative join の持ち上げを係数の充填へ帰着する。
方針：時間と係数を対にして区間付き対角への pullback を使う。
規約：係数の充填は明示的な入力。
使われ方：底の射影を保つ混合ホーンの充填。 -/
lemma relativeJoin_mixed_leftHorn_lift_of_coefficient {X Y : SSet.{u}} (n : ℕ)
    (i : Fin (n + 3)) (hi : i < Fin.last (n + 2)) (f : X ⟶ Y)
    (a : (horn (n + 2) i : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y))
    (t : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (ht : (horn (n + 2) i).ι ≫ t = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 Y))
    (ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1)
    (ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 ≤ n + 2)
    (c : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hc : (horn (n + 2) i).ι ≫ c = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 Y)) :
    ∃ l : (Δ[n + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y),
      (horn (n + 2) i).ι ≫ l = a ∧
      l ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) = lift t c := by
  let τ := lift t c
  have hτ : (horn (n + 2) i).ι ≫ τ =
      a ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      exact ht
    · rw [Category.assoc, lift_snd]
      exact hc
  let β := τ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y
  have hβ : (horn (n + 2) i).ι ≫ β =
      (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y) := by
    change ((horn (n + 2) i).ι ≫ τ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y = _
    rw [hτ, Category.assoc, ← pullback.condition, ← Category.assoc]
  have hbcut : (SSet.yonedaEquiv β).1.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 := by
    rw [SSet.yonedaEquiv_comp]
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y).app (Opposite.op ⦋n + 2⦌)
      (SSet.yonedaEquiv t, SSet.yonedaEquiv c)).1.val = _
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_app_cut Y (n + 2) _ _
  obtain ⟨d, hd, hdβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_right_id_mixed_leftHorn_hasLift n i hi f
    (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)) β hβ
    (by rw [hbcut]; exact ht0) (by rw [hbcut]; exact ht1)
  refine ⟨pullback.lift d τ hdβ, ?_, pullback.lift_snd _ _ _⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact hd
  · rw [Category.assoc, pullback.lift_snd]
    exact hτ

/-- 概要：終域が left fibration なら区間実現の混合した左ホーンは持ち上がる。
方針：終域への係数ホーンを充填し時間と組にして元の射影を保つ。
規約：欠ける面は最後以外、時間は両端にまたがる。
使われ方：任意の相対射を区間上の left fibration にする中心分岐。 -/
lemma relativeArrowCollage_mixed_leftHorn_hasLift {E F B : SSet.{u}}
    (f : E ⟶ F) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (n : ℕ)
    (i : Fin (n + 3)) (hi : i < Fin.last (n + 2))
    (a : (horn (n + 2) i : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 F))
    (b : (Δ[n + 2] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ B)
    (sq : CommSq a (horn (n + 2) i).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection f q) b)
    (ht0 : 0 < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut
      (stdSimplex.objEquiv (SSet.yonedaEquiv (b ≫ fst Δ[1] B))).toOrderHom 1)
    (ht1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut
      (stdSimplex.objEquiv (SSet.yonedaEquiv (b ≫ fst Δ[1] B))).toOrderHom 1 ≤ n + 2) :
    sq.HasLift := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
  have sqc : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 F)) (horn (n + 2) i).ι
      q (b ≫ snd Δ[1] B) := by
    constructor
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_snd, ← Category.assoc, sq.w,
      Category.assoc]
  have ht : (horn (n + 2) i).ι ≫ (b ≫ fst Δ[1] B) = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 F) := by
    rw [← Category.assoc, ← sq.w, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeArrowCollageProjection_fst]
  obtain ⟨l, hl, hlτ⟩ := relativeJoin_mixed_leftHorn_lift_of_coefficient n i hi f a
    (b ≫ fst Δ[1] B) ht ht0 ht1 sqc.lift sqc.fac_left
  refine CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := ?_ }
  change l ≫ (pullback.snd _ _ ≫ (Δ[1] ◁ q)) = b
  rw [← Category.assoc, hlτ]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, lift_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
    exact sqc.fac_right

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
