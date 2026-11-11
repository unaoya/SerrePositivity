module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalAnodyneAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
概要：right anodyne 性の引き戻し保存を、通常の引き戻し関手の右随伴の存在へ還元する。
方針：slice の右ホーンの像は既存の引き戻しの定理で処理し、持ち上げ性の随伴対応を使う。
規約：このファイルでは右随伴の存在は明示した仮定。SSetPullbackAdjoint・LeftFibrationAnodynePullback で解消する。
使われ方：Quillen A に必要な left fibration に沿う引き戻しの安定性。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：任意の引き戻し正方形で、left fibration に沿う右ホーンの引き戻しは right anodyne。
方針：標準の pullback の包含への同型を消去する。
規約：ホーン番号 k は零以外。
使われ方：slice の引き戻し関手の生成元での作用の検査。 -/
lemma leftFibration_rightHorn_isPullback_rightAnodyne
    {P E : SSet.{u}} (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (i : P ⟶ E) (a : P ⟶ (horn (n + 1) k : SSet.{u}))
    (hs : IsPullback i a p (horn (n + 1) k).ι) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i := by
  rw [← hs.isoPullback_hom_fst]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem _ _
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions hs.isoPullback.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_rightHorn_pullback_rightAnodyne n k hk p)

/-- 概要：右ホーンである任意の射の left fibration に沿う引き戻しは right anodyne。
方針：ホーンの生成元の構成子で標準形へ戻す。
規約：slice の対象の射影の等式について依存消去しない。
使われ方：slice の右ホーンの生成元を通常の射の性質で扱う。 -/
lemma cofinalRightHorn_isPullback_rightAnodyne {P E A D : SSet.{u}}
    (f : A ⟶ D) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions f) (p : E ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (i : P ⟶ E) (a : P ⟶ A) (hs : IsPullback i a p f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i := by
  rcases hf with ⟨k, hk⟩
  exact leftFibration_rightHorn_isPullback_rightAnodyne _ k (ne_of_gt hk) p i a hs

/-- 概要：通常の slice の引き戻し関手の射は元の射の引き戻し。
方針：二つの標準引き戻し正方形から右側を消去する。
規約：p と i の充填性は不要。
使われ方：全右ホーンの引き戻しの結果を slice の生成元に渡す。 -/
lemma cofinalOverPullback_map_isPullback {E B : SSet.{u}} (p : E ⟶ B)
    {A D : Over B} (i : A ⟶ D) :
    IsPullback ((Over.pullback p).map i).left (pullback.fst A.hom p)
      (pullback.fst D.hom p) i.left := by
  have hs : IsPullback
      (((Over.pullback p).map i).left ≫ pullback.snd D.hom p)
      (pullback.fst A.hom p) p (i.left ≫ D.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback A.hom p).flip
  exact hs.of_right (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback D.hom p).flip

/-- 概要：left fibration の slice 引き戻しは右ホーンを right anodyne な射に送る。
方針：射の引き戻し正方形と、底の left fibration の安定性を使う。
規約：通常の圏の slice の中の全ての底図式を検査する。
使われ方：生成元から一般の right anodyne な射への移送の入力。 -/
lemma leftFibration_overPullback_rightHorn_rightAnodyne {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {A D : Over B} (i : A ⟶ D)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions i.left) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions ((Over.pullback p).map i).left := by
  have hs := cofinalOverPullback_map_isPullback p i
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst D.hom p) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst D.hom p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  exact cofinalRightHorn_isPullback_rightAnodyne i.left hi _ _ _ hs

/-- 概要：通常の引き戻し関手に右随伴があれば、left fibration に沿う right anodyne 性が保存される。
方針：全右ホーンの結果を随伴の持ち上げ対応で一般の射に移す。
規約：IsLeftAdjoint の仮定は LeftFibrationAnodynePullback で解消する。
使われ方：引き戻し安定性の残る一般圏論的な条件を一箇所に集約する。 -/
lemma leftFibration_overPullback_rightAnodyne_of_isLeftAdjoint {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [(Over.pullback p).IsLeftAdjoint]
    {A D : Over B} (i : A ⟶ D) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i.left) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions ((Over.pullback p).map i).left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalRightAnodyne_leftAdjoint_of_horns (Adjunction.ofIsLeftAdjoint (Over.pullback p))
    (fun j hj ↦ leftFibration_overPullback_rightHorn_rightAnodyne p j hj) i hi

/-- 概要：依存積が存在すれば left fibration に沿う任意の right anodyne な射の引き戻しも right anodyne。
方針：底の恒等射への slice の射を引き戻し、同型な終域を消去して第一射影へ移す。
規約：右随伴の存在の仮定を明示した中間定理。無条件版は LeftFibrationAnodynePullback。
使われ方：通常の前層圏の依存積の構成後に無条件の引き戻し保存を公開する。 -/
lemma leftFibration_pullback_rightAnodyne_of_isLeftAdjoint {E A B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [(Over.pullback p).IsLeftAdjoint]
    (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (pullback.fst p f) := by
  let i : Over.mk f ⟶ Over.mk (𝟙 B) := Over.homMk f (by simp)
  have h := leftFibration_overPullback_rightAnodyne_of_isLeftAdjoint p i hf
  have h' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (pullback.snd f p) := by
    have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem ((Over.pullback p).map i).left
      (pullback.snd (𝟙 B) p) h (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions _)
    have he : ((Over.pullback p).map i).left ≫ pullback.snd (𝟙 B) p =
        pullback.snd f p := by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      exact pullback.lift_snd _ _ _
    exact he ▸ hs
  rw [← pullbackSymmetry_hom_comp_snd p f]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem _ _
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (pullbackSymmetry p f).hom) h'

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
