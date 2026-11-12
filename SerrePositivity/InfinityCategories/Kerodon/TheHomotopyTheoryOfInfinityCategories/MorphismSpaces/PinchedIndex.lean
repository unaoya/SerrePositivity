module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-! # 右 pinched 成分の有限集合の添字

概要：非空集合 J に最終頂点を加えた dg nerve の成分の添字を記述する。
方針：先頭頂点を castSucc で埋め込み、追加した最終点を insert する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形成分と dg nerve 成分の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：先頭の集合 J に追加した最終頂点を含めた集合。
方針：castSucc による像に最終点を挿入する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：次数 1−|J| の射の添字。 -/
def withLast {n : ℕ} (J : Finset (Fin (n + 1))) : Finset (Fin (n + 2)) :=
  insert (Fin.last (n + 1)) (J.image Fin.castSucc)

/-- 概要：先頭頂点の像は最終点を含まない。
方針：castSucc の値が最終点より真に小さいことを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：濃度と端点の計算。 -/
lemma last_not_mem_image {n : ℕ} (J : Finset (Fin (n + 1))) :
    Fin.last (n + 1) ∉ J.image Fin.castSucc := by
  rintro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact (Fin.ne_of_lt (Fin.castSucc_lt_last i)) hi

/-- 概要：最終点を加えると濃度が一増える。
方針：最終点が像に属さず、castSucc が単射であることを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：dg nerve の次数と線形成分の次数の一致。 -/
lemma card_withLast {n : ℕ} (J : Finset (Fin (n + 1))) :
    (withLast J).card = J.card + 1 := by
  rw [withLast, Finset.card_insert_of_notMem (last_not_mem_image J),
    Finset.card_image_of_injective _ (Fin.castSucc_injective _)]

/-- 概要：非空集合に最終点を加えると二点以上になる。
方針：元の集合の正の濃度と挿入による濃度増加を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：dg nerve の hom の濃度条件。 -/
lemma two_withLast {n : ℕ} {J : Finset (Fin (n + 1))} (hJ : J.Nonempty) :
    2 ≤ (withLast J).card := by
  have := Finset.card_pos.mpr hJ
  rw [card_withLast]
  omega

/-- 概要：最終点を加えた集合の最小点は元の最小点の先頭埋め込み。
方針：元の最小性と全先頭点が最終点より小さいことを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：dg 成分の始点。 -/
lemma min_withLast {n : ℕ} {J : Finset (Fin (n + 1))} (hJ : J.Nonempty)
    (h : (withLast J).Nonempty) : (J.min' hJ).castSucc = (withLast J).min' h := by
  symm
  apply (Finset.isLeast_min' _ h).unique
  refine ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, J.min'_mem hJ, rfl⟩), ?_⟩
  intro j hj
  rcases Finset.mem_insert.mp hj with hlast | hj
  · subst j
    exact Fin.le_last _
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Fin.castSucc_le_castSucc_iff.mpr ((J.isLeast_min' hJ).2 hi)

/-- 概要：最終点を加えた集合の最大点は最終点。
方針：最終点の所属と Fin の最大性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：dg 成分の終点。 -/
lemma max_withLast {n : ℕ} (J : Finset (Fin (n + 1))) (h : (withLast J).Nonempty) :
    Fin.last (n + 1) = (withLast J).max' h := by
  symm
  apply (Finset.isGreatest_max' _ h).unique
  exact ⟨Finset.mem_insert_self _ _, fun _ _ => Fin.le_last _⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
