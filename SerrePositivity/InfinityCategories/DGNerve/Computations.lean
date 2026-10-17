module
public import SerrePositivity.InfinityCategories.DGNerve.Basic

/-! # dg nerve の面・退化の成分計算

概要：面は像の成分で評価し、退化は単射・潰れた辺・高次の三分岐で評価する。
方針：単体的構造とデータの引き戻しの定義を既存の成分補題に接続する。
規約：HA Construction 1.3.1.6。使われ方：ホーンの貼合せとホモトピー圏の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.dgNerve

open CategoryTheory DifferentialGraded
open DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：面のデータは対応する順序埋め込みによる引き戻し。
方針：単体的構造の定義の評価。
規約：HA Construction 1.3.1.6。使われ方：面の全成分の計算。 -/
lemma δ_data {n : ℕ} (i : Fin (n + 2)) (s : (dgNerve A D) _⦋n + 1⦌) :
    ((dgNerve A D).δ i s).toSimplexData =
      s.toSimplexData.pullback i.succAboveOrderEmb.toOrderHom := rfl

/-- 概要：退化のデータは基本全射による引き戻し。
方針：単体的構造の定義の評価。
規約：HA Construction 1.3.1.6。使われ方：退化の全成分の計算。 -/
lemma σ_data {n : ℕ} (i : Fin (n + 1)) (s : (dgNerve A D) _⦋n⦌) :
    ((dgNerve A D).σ i s).toSimplexData = s.toSimplexData.pullback i.predAboveOrderHom := rfl

/-- 概要：面の成分は、飛ばした頂点以外の像の成分。
方針：面の写像は全域単射なので、単射分岐の評価を使う。
規約：HA Construction 1.3.1.6。使われ方：ホーンから成分を回収する際の面との比較。 -/
lemma δ_hom {n : ℕ} (i : Fin (n + 2)) (s : (dgNerve A D) _⦋n + 1⦌)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    let α := i.succAboveOrderEmb.toOrderHom
    ((dgNerve A D).δ i s).hom J a b k hJ ha hb hk =
      s.hom (J.image α) (α a) (α b) k (Index.image_two i.succAboveOrderEmb.injective.injOn hJ)
        (Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
        (Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
        (by
          have hi : Set.InjOn α (J : Set (Fin (n + 1))) := i.succAboveOrderEmb.injective.injOn
          rw [Finset.card_image_of_injOn hi]
          exact hk) :=
  s.toSimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ i.succAboveOrderEmb.injective.injOn

/-- 概要：退化写像が J 上単射なら、成分は像の成分である。
方針：三分岐の単射の場合を評価する。
規約：HA Construction 1.3.1.6。使われ方：退化で潰れない成分の計算。 -/
lemma σ_hom_of_inj {n : ℕ} (i : Fin (n + 1)) (s : (dgNerve A D) _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ))
    (hi : Set.InjOn i.predAboveOrderHom (J : Set (Fin (n + 2)))) :
    let α := i.predAboveOrderHom
    ((dgNerve A D).σ i s).hom J a b k hJ ha hb hk =
      s.hom (J.image α) (α a) (α b) k (Index.image_two hi hJ)
        (Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
        (Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk) :=
  s.toSimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ hi

/-- 概要：重複二点を含む高次成分は退化によって零になる。
方針：重複二点の像が等しいことから非単射性を得て、第三分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：退化した三角形以上の成分の消去。 -/
lemma σ_hom_eq_zero {n : ℕ} (i : Fin (n + 1)) (s : (dgNerve A D) _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hp : i.castSucc ∈ J) (hq : i.succ ∈ J)
    (hc : J.card ≠ 2) : ((dgNerve A D).σ i s).hom J a b k hJ ha hb hk = 0 := by
  exact s.toSimplexData.pullback_hom_of_not_inj i.predAboveOrderHom J a b k hJ ha hb hk
    (Index.not_injOn_of_equal hp hq (ne_of_lt Fin.castSucc_lt_succ) (by simp)) hc

/-- 概要：潰れた辺の成分は単位と異種等号で一致する。
方針：重複二点による非単射性と、単位分岐の評価を使う。
規約：HA Construction 1.3.1.6。使われ方：退化辺と恒等射の同定。 -/
lemma σ_hom_of_collapsed_pair {n : ℕ} (i : Fin (n + 1)) (s : (dgNerve A D) _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hp : i.castSucc ∈ J) (hq : i.succ ∈ J)
    (hc : J.card = 2) : HEq (((dgNerve A D).σ i s).hom J a b k hJ ha hb hk)
      (unitElement A (s.obj (i.predAboveOrderHom b))).val := by
  exact s.toSimplexData.pullback_hom_of_collapsed_pair i.predAboveOrderHom J a b k hJ ha hb hk
    (Index.not_injOn_of_equal hp hq (ne_of_lt Fin.castSucc_lt_succ) (by simp)) hc

end SerrePositivity.InfinityCategories.dgNerve
