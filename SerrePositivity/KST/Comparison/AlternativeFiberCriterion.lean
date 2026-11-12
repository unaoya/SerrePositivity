module

public import SerrePositivity.KST.Comparison.FibrantSquareCriterion
public import SerrePositivity.KST.Comparison.HomotopyPullbackThreeInputs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 任意の厳密な引き戻しによるホモトピー引き戻しの判定

概要：右射の別分解に対する比較を、選択された標準引き戻し以外でも判定する。
方針：実際の引き戻しの普遍性から標準引き戻しとの同型を合成する。
規約：Segal 1974 Proposition 1.6 の順序余極限の段階の補助。
使われ方：図式圏の引き戻しを次数評価または余極限へ送った対象との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：別分解の厳密な引き戻しへの任意の整合する比較でホモトピー引き戻しを判定できる。
方針：比較と引き戻しの標準同型の合成を標準比較と同定する。
規約：分解の前半には局所化同型、後半には Kan fibration を要求する。
使われ方：引き戻しを保存する関手を適用した後の比較。
-/
@[kerodon 010N]
theorem isHomotopyPullback_iff_alternative_fiber
    {A X Y B E P : SSet.{u}} {a : A ⟶ X} {b : A ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : CommSq a b f g)
    (i : X ⟶ E) (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
    (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p) (hfac : i ≫ p = f)
    {r : P ⟶ Y} {s : P ⟶ E} (hpb : IsPullback r s g p)
    (k : A ⟶ P) (hr : k ≫ r = b) (hs : k ≫ s = a ≫ i) :
    IsHomotopyPullback sq ↔ IsIso (AnodyneHomotopy.anodyneQ.map k) := by
  have he : k ≫ hpb.isoPullback.hom =
      alternativePullbackComparison sq.flip i p hfac := by
    apply pullback.hom_ext
    · rw [Category.assoc, hpb.isoPullback_hom_fst, hr]
      exact (alternativePullbackComparison_fst ..).symm
    · rw [Category.assoc, hpb.isoPullback_hom_snd, hs]
      exact (alternativePullbackComparison_snd ..).symm
  let sqi : CommSq (a ≫ i) b p g := ⟨by rw [Category.assoc, hfac]; exact sq.w⟩
  have hc : IsHomotopyPullback sq ↔ IsHomotopyPullback sqi := by
    apply isHomotopyPullback_iff_of_localized_isIso sq sqi
      (𝟙 A) i (𝟙 Y) (𝟙 B) (by simp) (by simp) ?_ (by simp)
      (by infer_instance) hi (by infer_instance) (by infer_instance)
    simpa only [Category.comp_id] using hfac.symm
  calc
    _ ↔ IsHomotopyPullback sqi := hc
    _ ↔ IsIso (AnodyneHomotopy.anodyneQ.map
        (alternativePullbackComparison sq.flip i p hfac)) :=
      isHomotopyPullback_iff_strict_of_left_fibration sqi hp
    _ ↔ IsIso (AnodyneHomotopy.anodyneQ.map k) := by
      rw [← he, Functor.map_comp]
      exact isIso_comp_right_iff _ _

end SerrePositivity.KST.Comparison
