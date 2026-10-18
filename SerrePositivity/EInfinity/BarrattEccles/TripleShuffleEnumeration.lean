module

public import SerrePositivity.EInfinity.BarrattEccles.TripleShuffleEdges

/-!
# 三入力の shuffle の各色の昇順列挙

概要：Berger–Fresse §1.1.3 の二つの括弧付けで各色の辺番号が一致することを示す。
方針：各色の辺集合の一致と昇順列挙の一意性を使う。
規約：加法の結合則による移送は辺番号の値を変えない。
使われ方：反復 shuffle 置換の等式と符号の積の一致を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：最初の色の辺の二段の列挙は添字替え後の列挙と一致する（Berger–Fresse §1.1.3）。
方針：最初の色の辺集合の等式に昇順列挙の一意性を適用する。
規約：両方の列挙の入力は Fin p である。
使われ方：三入力の shuffle 置換の最初のブロックを比較する。 -/
lemma tripleShuffle_first_enumeration (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin p) :
    Fin.cast (Nat.add_assoc p q r)
        (v.1.val.orderEmbOfFin v.1.property (v.2.val.orderEmbOfFin v.2.property a)) =
      (tripleShuffleEquiv p q r v).1.val.orderEmbOfFin
        (tripleShuffleEquiv p q r v).1.property a := by
  apply orderEmbOfFin_eq_of_map_eq v.2.val (tripleShuffleEquiv p q r v).1.val
    v.2.property (tripleShuffleEquiv p q r v).1.property
    ((v.1.val.orderEmbOfFin v.1.property).trans
      (Fin.castOrderIso (Nat.add_assoc p q r)).toOrderEmbedding)
    (OrderIso.refl _).toOrderEmbedding ?_ a
  have h := (tripleShuffle_firstEdges p q r v).symm
  change (v.2.val.map (v.1.val.orderEmbOfFin v.1.property).toEmbedding).map
    (finCongr (Nat.add_assoc p q r)).toEmbedding = _ at h
  have he : ((v.1.val.orderEmbOfFin v.1.property).trans
      (Fin.castOrderIso (Nat.add_assoc p q r)).toOrderEmbedding).toEmbedding =
      (v.1.val.orderEmbOfFin v.1.property).toEmbedding.trans
        (finCongr (Nat.add_assoc p q r)).toEmbedding := by ext x; rfl
  have hid : (OrderIso.refl (Fin (p + (q + r)))).toOrderEmbedding.toEmbedding =
      Function.Embedding.refl _ := by ext x; rfl
  rw [he, hid, Finset.map_refl]
  simpa only [Finset.map_map] using h

/-- 概要：二番目の色の辺の二段の列挙は添字替え後の列挙と一致する（Berger–Fresse §1.1.3）。
方針：二番目の色の辺集合の等式に昇順列挙の一意性を適用する。
規約：両方の列挙の入力は Fin q である。
使われ方：三入力の shuffle 置換の二番目のブロックを比較する。 -/
lemma tripleShuffle_second_enumeration (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin q) :
    Fin.cast (Nat.add_assoc p q r)
        (v.1.val.orderEmbOfFin v.1.property (v.2.valᶜ.orderEmbOfFin v.2.compl_card a)) =
      (tripleShuffleEquiv p q r v).1.valᶜ.orderEmbOfFin
        (tripleShuffleEquiv p q r v).1.compl_card
        ((tripleShuffleEquiv p q r v).2.val.orderEmbOfFin
          (tripleShuffleEquiv p q r v).2.property a) := by
  apply orderEmbOfFin_eq_of_map_eq v.2.valᶜ (tripleShuffleEquiv p q r v).2.val
    v.2.compl_card (tripleShuffleEquiv p q r v).2.property
    ((v.1.val.orderEmbOfFin v.1.property).trans
      (Fin.castOrderIso (Nat.add_assoc p q r)).toOrderEmbedding)
    ((tripleShuffleEquiv p q r v).1.valᶜ.orderEmbOfFin
      (tripleShuffleEquiv p q r v).1.compl_card) ?_ a
  have h := (tripleShuffle_secondEdges p q r v).symm
  change (v.2.valᶜ.map (v.1.val.orderEmbOfFin v.1.property).toEmbedding).map
    (finCongr (Nat.add_assoc p q r)).toEmbedding =
      (tripleShuffleEquiv p q r v).2.val.map
        ((tripleShuffleEquiv p q r v).1.valᶜ.orderEmbOfFin
          (tripleShuffleEquiv p q r v).1.compl_card).toEmbedding at h
  have he : ((v.1.val.orderEmbOfFin v.1.property).trans
      (Fin.castOrderIso (Nat.add_assoc p q r)).toOrderEmbedding).toEmbedding =
      (v.1.val.orderEmbOfFin v.1.property).toEmbedding.trans
        (finCongr (Nat.add_assoc p q r)).toEmbedding := by ext x; rfl
  rw [he]
  simpa only [Finset.map_map] using h

/-- 概要：三番目の色の辺の列挙は添字替え後の二段の列挙と一致する（Berger–Fresse §1.1.3）。
方針：三番目の色の辺集合の等式に昇順列挙の一意性を適用する。
規約：両方の列挙の入力は Fin r である。
使われ方：三入力の shuffle 置換の最後のブロックを比較する。 -/
lemma tripleShuffle_third_enumeration (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin r) :
    Fin.cast (Nat.add_assoc p q r) (v.1.valᶜ.orderEmbOfFin v.1.compl_card a) =
      (tripleShuffleEquiv p q r v).1.valᶜ.orderEmbOfFin
        (tripleShuffleEquiv p q r v).1.compl_card
        ((tripleShuffleEquiv p q r v).2.valᶜ.orderEmbOfFin
          (tripleShuffleEquiv p q r v).2.compl_card a) := by
  apply orderEmbOfFin_eq_of_map_eq v.1.valᶜ (tripleShuffleEquiv p q r v).2.valᶜ
    v.1.compl_card (tripleShuffleEquiv p q r v).2.compl_card
    (Fin.castOrderIso (Nat.add_assoc p q r)).toOrderEmbedding
    ((tripleShuffleEquiv p q r v).1.valᶜ.orderEmbOfFin
      (tripleShuffleEquiv p q r v).1.compl_card) ?_ a
  exact (tripleShuffle_thirdEdges p q r v).symm

end SerrePositivity.EInfinity.BarrattEccles
