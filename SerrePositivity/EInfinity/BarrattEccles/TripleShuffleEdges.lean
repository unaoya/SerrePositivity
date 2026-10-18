module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFlags
public import SerrePositivity.EInfinity.BarrattEccles.OrderedSubsetEnumeration

/-!
# 三入力の shuffle の各色の辺集合

概要：Berger–Fresse §1.1.3 の反復 shuffle の二番目と三番目の色の辺集合を同定する。
方針：最初の二色の集合から最初の色を除き、残りの色には補集合を使う。
規約：全辺数の括弧の変更は finCongr による map で行う。
使われ方：三入力の shuffle 置換の各ブロックを比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：三入力の添字替えは二番目の色の辺集合を保つ（Berger–Fresse §1.1.3）。
方針：最初の二色の辺集合から最初の色の辺集合を引く。
規約：左括弧では内側の垂直辺、右括弧では内側の水平辺である。
使われ方：二番目の色の昇順列挙と shuffle 置換を比較する。 -/
lemma tripleShuffle_secondEdges (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    ((orderedSubsetEquiv (tripleShuffleEquiv p q r v).1.valᶜ
        (tripleShuffleEquiv p q r v).1.compl_card) (tripleShuffleEquiv p q r v).2.val).val =
      ((orderedSubsetEquiv v.1.val v.1.property) v.2.valᶜ).val.map
        (finCongr (Nat.add_assoc p q r)).toEmbedding := by
  let w := tripleShuffleEquiv p q r v
  let D := orderedSubsetEquiv w.1.valᶜ w.1.compl_card w.2.val
  have hd : Disjoint w.1.val D.val := Finset.disjoint_left.mpr (by
    intro x hx hxD
    exact (Finset.mem_compl.mp (D.property hxD)) hx)
  have h := Finset.union_sdiff_cancel_left hd
  change (w.1.val ∪ D.val) \ w.1.val = D.val at h
  conv_lhs at h => rw [tripleShuffle_firstTwoEdges, tripleShuffle_firstEdges,
    ← Finset.map_sdiff, ← orderedSubsetEquiv_compl]
  exact h.symm

/-- 概要：三入力の添字替えは三番目の色の辺集合を保つ（Berger–Fresse §1.1.3）。
方針：右括弧の最初の二色の補集合を計算する。
規約：左括弧では外側の垂直辺、右括弧では二段の垂直辺である。
使われ方：三番目の色の昇順列挙と shuffle 置換を比較する。 -/
lemma tripleShuffle_thirdEdges (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    ((orderedSubsetEquiv (tripleShuffleEquiv p q r v).1.valᶜ
        (tripleShuffleEquiv p q r v).1.compl_card) (tripleShuffleEquiv p q r v).2.valᶜ).val =
      v.1.valᶜ.map (finCongr (Nat.add_assoc p q r)).toEmbedding := by
  rw [orderedSubsetEquiv_compl]
  have h := congrArg (fun S : Finset (Fin (p + (q + r))) => Sᶜ)
    (tripleShuffle_firstTwoEdges p q r v)
  have hleft : (tripleShuffleEquiv p q r v).1.valᶜ \
      ((orderedSubsetEquiv (tripleShuffleEquiv p q r v).1.valᶜ
        (tripleShuffleEquiv p q r v).1.compl_card) (tripleShuffleEquiv p q r v).2.val).val =
      ((tripleShuffleEquiv p q r v).1.val ∪
        ((orderedSubsetEquiv (tripleShuffleEquiv p q r v).1.valᶜ
          (tripleShuffleEquiv p q r v).1.compl_card) (tripleShuffleEquiv p q r v).2.val).val)ᶜ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_union, not_or]
  rw [hleft, h]
  ext x
  simp only [Finset.mem_compl, Finset.mem_map_equiv]

end SerrePositivity.EInfinity.BarrattEccles
