module
public import SerrePositivity.InfinityCategories.Stable.Pasting
public import SerrePositivity.InfinityCategories.F1.SquareOpposite

/-! # 引き戻し四角形の貼り合わせ

概要：右が引き戻しなら、左が引き戻しであることと外側が引き戻しであることは同値。
方針：長方形と値域を反転し、join・slice で証明した押し出しの貼り合わせを適用する。
規約：HTT Lemma 4.4.2.1。安定性を仮定しない。
使われ方：S4 の fiber 列の貼り合わせと八面体。
-/
@[expose] public section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右が引き戻しなら左と外側の引き戻し性は同値。
方針：面を反転して押し出しの貼り合わせの同値へ帰着する。
規約：値域は quasicategory、面二が左、零が右、一が外側。
使われ方：HTT Lemma 4.4.2.1 と fiber の合成。 -/
lemma isPullbackSquare_pasting_iff {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hright : IsPullbackSquare (pastingSquare F 0)) :
    IsPullbackSquare (pastingSquare F 2) ↔ IsPullbackSquare (pastingSquare F 1) := by
  have hl : IsPushoutSquare (pastingSquare (reverseGrid F) 2) := by
    rw [reverseGrid_pastingSquare]
    exact (isPullbackSquare_iff_reverseGrid (pastingSquare F 0)).mp hright
  have h := isPushoutSquare_pasting_iff (reverseGrid F) hl
  rw [reverseGrid_pastingSquare, reverseGrid_pastingSquare] at h
  exact (isPullbackSquare_iff_reverseGrid (pastingSquare F 2)).trans
    (h.trans (isPullbackSquare_iff_reverseGrid (pastingSquare F 1)).symm)

/-- 概要：隣り合う二つの引き戻し四角形の外側は引き戻し。
方針：右を固定した左と外側の判定の順方向を使う。
規約：実際の単体的な長方形を指定。使われ方：fiber 列の貼り合わせ。 -/
lemma isPullbackSquare_pasting {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hleft : IsPullbackSquare (pastingSquare F 2))
    (hright : IsPullbackSquare (pastingSquare F 0)) : IsPullbackSquare (pastingSquare F 1) :=
  (isPullbackSquare_pasting_iff F hright).mp hleft

/-- 概要：右と外側が引き戻しなら左四角形も引き戻し。
方針：右を固定した同値判定の逆方向を使う。
規約：値域は quasicategory。使われ方：八面体に現れる fiber の判定。 -/
lemma isPullbackSquare_pasting_cancel_right {X : SSet.{u}} [Quasicategory X]
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hright : IsPullbackSquare (pastingSquare F 0))
    (houter : IsPullbackSquare (pastingSquare F 1)) : IsPullbackSquare (pastingSquare F 2) :=
  (isPullbackSquare_pasting_iff F hright).mpr houter

end SerrePositivity.InfinityCategories
