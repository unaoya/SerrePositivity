module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedIndex

/-! # 最終頂点を含む成分の先頭集合の回復

概要：有限集合から最終点を除き、先頭頂点の添字へ戻す。
方針：castSucc の逆像を有限集合として取り、像・濃度・最小点を計算する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形族からの単体データの再構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：集合の先頭頂点だけを一段小さい添字で取り出す。
方針：全先頭添字のうち castSucc が元の集合に属するものを選ぶ。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形族を評価する集合の回復。 -/
def withoutLast {n : ℕ} (I : Finset (Fin (n + 2))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => i.castSucc ∈ I)

/-- 概要：先頭集合の像は元の集合から最終点を消した集合。
方針：最終点と先頭点の二つの場合で所属を比較する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：元の成分集合の復元。 -/
lemma image_withoutLast {n : ℕ} (I : Finset (Fin (n + 2))) :
    (withoutLast I).image Fin.castSucc = I.erase (Fin.last (n + 1)) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp [withoutLast, ne_of_lt (Fin.castSucc_lt_last i)]

/-- 概要：最終点を含む集合は先頭集合に最終点を加えると復元される。
方針：先頭集合の像の計算と削除した点の再挿入を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：再構成する成分の添字の同定。 -/
lemma withLast_withoutLast {n : ℕ} (I : Finset (Fin (n + 2))) (h : Fin.last (n + 1) ∈ I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast (withoutLast I) = I := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast, image_withoutLast, Finset.insert_erase h]

/-- 概要：先頭集合に最終点を加えてから取り出すと元に戻る。
方針：castSucc の像の所属を計算する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形族を再構成して回収したときの逆則。 -/
lemma withoutLast_withLast {n : ℕ} (J : Finset (Fin (n + 1))) :
    withoutLast (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) = J := by
  ext j
  simp [withoutLast, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast]

/-- 概要：最終点を含む集合の濃度は先頭集合の濃度より一大きい。
方針：集合の復元と最終点追加の濃度計算を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：再構成する射の次数。 -/
lemma card_withoutLast {n : ℕ} (I : Finset (Fin (n + 2))) (h : Fin.last (n + 1) ∈ I) :
    I.card = (withoutLast I).card + 1 := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast, withLast_withoutLast I h]

/-- 概要：二点以上で最終点を含む集合の先頭集合は非空。
方針：濃度の一つの減少を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形族の非空添字条件。 -/
lemma withoutLast_nonempty {n : ℕ} {I : Finset (Fin (n + 2))} (hI : 2 ≤ I.card)
    (h : Fin.last (n + 1) ∈ I) : (withoutLast I).Nonempty := by
  apply Finset.card_pos.mp
  have := card_withoutLast I h
  omega

/-- 概要：二点以上の集合の最小点は最終点ではない。
方針：最小点が最大点より真に小さく、最大点が最終点以下であることを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：再構成する射の始点が x であること。 -/
lemma min_ne_last {n : ℕ} (I : Finset (Fin (n + 2))) (hI : 2 ≤ I.card) :
    I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) ≠ Fin.last (n + 1) := by
  exact ne_of_lt ((I.min'_lt_max'_of_card (by omega)).trans_le (Fin.le_last _))

/-- 概要：先頭集合の最小点の像は元の集合の最小点。
方針：先頭の最小性を埋め込み、最終点との比較では最大性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：回収と再構成の始点の一致。 -/
lemma min_withoutLast {n : ℕ} (I : Finset (Fin (n + 2))) (hI : 2 ≤ I.card)
    (h : Fin.last (n + 1) ∈ I) :
    ((withoutLast I).min' (withoutLast_nonempty hI h)).castSucc = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
  symm
  apply (I.isLeast_min' _).unique
  refine ⟨?_, ?_⟩
  · exact (Finset.mem_filter.mp ((withoutLast I).min'_mem _)).2
  · intro i hi
    induction i using Fin.lastCases with
    | last => exact Fin.le_last _
    | cast i =>
      apply Fin.castSucc_le_castSucc_iff.mpr
      exact ((withoutLast I).isLeast_min' _).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
