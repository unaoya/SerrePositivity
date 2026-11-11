module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderPullbackLift

/-!
概要：relative join と係数の任意の底変換の交換。
方針：join の両因子の pullback の保存を定義の pullback と貼り、係数射影を合成する。
規約：底変換の射 h に条件を課さない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各単体上の比較を一般の終域の比較へ移す同定。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：区間付きの底変換は係数射影に関して pullback。
方針：各次数で時刻を保ち、与えられた新しい係数を組にして持ち上げる。
規約：区間は左因子。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、区間付きの底から係数の底への移送。 -/
lemma prismBaseChange_isPullback {Y Z : SSet.{u}} (h : Z ⟶ Y) :
    IsPullback ((Δ[1] : SSet.{u}) ◁ h) (snd (Δ[1] : SSet.{u}) Z)
      (snd (Δ[1] : SSet.{u}) Y) h := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (whiskerLeft_snd (Δ[1] : SSet.{u}) h) n, ?_, ?_⟩
  · rintro ⟨t, z⟩ ⟨s, w⟩ ⟨h₁, h₂⟩
    change (t, h.app n z) = (s, h.app n w) at h₁
    exact Prod.ext (congrArg (fun a : (Δ[1] : SSet.{u}).obj n × Y.obj n ↦ a.1) h₁) h₂
  · rintro ⟨t, y⟩ z he
    exact ⟨⟨t, z⟩, Prod.ext rfl he.symm, rfl⟩

/-- 概要：relative join の底変換は区間付き係数の射影に関して pullback。
方針：構造射の pullback と右因子の自明な pullback の join を定義の pullback と横に貼る。
規約：対角の自然性で下辺を区間付き底変換と対角に分解する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の係数の底変換の中間段階。 -/
lemma relativeJoinPullbackMap_prism_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap f h)
      (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd f h) (𝟙 Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Z))
      (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y)) ((Δ[1] : SSet.{u}) ◁ h) := by
  have hZ : IsPullback h (𝟙 Z) (𝟙 Y) h := IsPullback.of_vert_isIso ⟨by simp⟩
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_isPullback (IsPullback.of_hasPullback f h) hZ
  have ht := (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd f h) (𝟙 Z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Z)).paste_horiz hj
  have ho : IsPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap f h ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y))
      (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (pullback.snd f h) (𝟙 Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (((Δ[1] : SSet.{u}) ◁ h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality]
    exact ht
  exact ho.of_right (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap_snd f h)
    (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y))

/-- 概要：relative join の底変換は係数の底への射影に関して pullback。
方針：区間付き係数の pullback と係数射影の pullback を縦に貼る。
規約：上辺と左辺は既存の標準比較と係数射影。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join と任意の底変換の交換。 -/
lemma relativeJoinPullbackMap_isPullback {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap f h) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection (pullback.snd f h) (𝟙 Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 Y)) h :=
  (relativeJoinPullbackMap_prism_isPullback f h).paste_vert (prismBaseChange_isPullback h)

/-- 概要：底変換した relative join から係数射影の pullback への標準射は同型。
方針：pullback の正方形の標準同型と両射影で一致させる。
規約：同型性は既存の標準の持ち上げそのものについて述べる。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、局所判定の pullback を具体的な relative join に戻す。 -/
instance relativeJoinPullbackLift_isIso {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackLift f h) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackLift f h =
      (relativeJoinPullbackMap_isPullback f h).flip.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackLift_fst, IsPullback.isoPullback_hom_fst]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackLift_snd, IsPullback.isoPullback_hom_snd]
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
