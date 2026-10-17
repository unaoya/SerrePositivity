module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedComponents
public import SerrePositivity.InfinityCategories.DGNerve.HornComponents

/-! # 右 pinched 単体の先頭面の成分

概要：先頭面が定値である条件から、その辺が dg 単位、高次成分が零であることを導く。
方針：先頭面への引き戻しを単射分岐で計算し、定値単体の三分岐と比較する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：dg nerve 方程式の線形化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.PinchedHom

open CategoryTheory DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：二点以上の部分集合上では零単体への定値写像は非単射。
方針：集合中の相異なる二点が同じ値に写ることを使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：定値単体の零・単位分岐。 -/
lemma not_injOn_constant {n : ℕ} {J : Finset (Fin (n + 1))} (hJ : 2 ≤ J.card) :
    ¬ Set.InjOn (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom (J : Set (Fin (n + 1))) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < J.card by omega)
  intro hi
  exact hab (hi ha hb rfl)

/-- 概要：定値 dg nerve 単体の高次成分は零。
方針：零単体への引き戻しの非単射・濃度二以外の分岐を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：先頭面の高次成分の消去。 -/
lemma constant_hom_zero {n : ℕ} (x : D) (J : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card ≠ 2) :
    (InfinityCategories.PinchedHom.constant (X := dgNerve A D) (Simplex.vertex x) n).hom
      J a b k hJ ha hb hk = 0 := by
  exact SimplexData.pullback_hom_of_not_inj (Simplex.vertex x).toSimplexData
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom J a b k hJ ha hb hk (not_injOn_constant hJ) hc

/-- 概要：定値 dg nerve 単体の辺成分は dg 単位。
方針：零単体への引き戻しで潰れた二点の単位分岐を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：線形化で現れる単位との合成。 -/
lemma constant_hom_unit {n : ℕ} (x : D) (J : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card = 2) :
    HEq ((InfinityCategories.PinchedHom.constant (X := dgNerve A D) (Simplex.vertex x) n).hom
      J a b k hJ ha hb hk) (unitElement A x).val := by
  exact SimplexData.pullback_hom_of_collapsed_pair (Simplex.vertex x).toSimplexData
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom J a b k hJ ha hb hk (not_injOn_constant hJ) hc

/-- 概要：先頭頂点の像の成分は定値面の同じ成分と異種等号で一致する。
方針：定値面の等式を成分で評価し、先頭面の単射分岐で計算する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：先頭面の全成分の同定。 -/
lemma front_hom_heq {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq (s.val.hom (J.image Fin.castSucc) a.castSucc b.castSucc k
      (Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (Index.image_min Fin.castSuccOrderEmb.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max Fin.castSuccOrderEmb.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hk))
      ((InfinityCategories.PinchedHom.constant (X := dgNerve A D) (Simplex.vertex x) n).hom
        J a b k hJ ha hb hk) := by
  have he := Simplex.hom_heq_of_eq s.source J a b k hJ ha hb hk
  change HEq ((s.val.toSimplexData.pullback Fin.castSuccOrderEmb.toOrderHom).hom
    J a b k hJ ha hb hk) _ at he
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ (Fin.castSucc_injective _).injOn] at he
  exact he

/-- 概要：右 pinched 単体の先頭面の高次成分は零。
方針：先頭面の成分の比較と定値単体の高次成分の零を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：線形方程式で高次切断合成を消す。 -/
lemma front_hom_zero {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card ≠ 2) :
    s.val.hom (J.image Fin.castSucc) a.castSucc b.castSucc k
      (Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (Index.image_min Fin.castSuccOrderEmb.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max Fin.castSuccOrderEmb.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hk) = 0 := by
  have he := front_hom_heq s J a b k hJ ha hb hk
  rw [constant_hom_zero x J a b k hJ ha hb hk hc] at he
  have hz : HEq (0 : GradedHom A x x k)
      (0 : GradedHom A (s.val.obj a.castSucc) (s.val.obj b.castSucc) k) := by
    rw [source_obj s a, source_obj s b]
  exact eq_of_heq (he.trans hz)

/-- 概要：右 pinched 単体の先頭面の辺成分は dg 単位。
方針：先頭面の成分の比較と定値単体の単位の計算を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：最初の削除項を単位との合成から得る。 -/
lemma front_hom_unit {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card = 2) :
    HEq (s.val.hom (J.image Fin.castSucc) a.castSucc b.castSucc k
      (Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (Index.image_min Fin.castSuccOrderEmb.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max Fin.castSuccOrderEmb.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hk))
      (unitElement A x).val :=
  (front_hom_heq s J a b k hJ ha hb hk).trans (constant_hom_unit x J a b k hJ ha hb hk hc)

/-- 概要：先頭面の高次成分を先に作用させる合成は零。
方針：先頭面の高次成分の零と通常順合成の零保存を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：線形化における高次切断の消去。 -/
lemma compose_front_hom_zero {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card ≠ 2) {z : D} {q t : ℤ}
    (g : GradedHom A (s.val.obj b.castSucc) z q) (ht : k + q = t) :
    compose A g (s.val.hom (J.image Fin.castSucc) a.castSucc b.castSucc k
      (Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (Index.image_min Fin.castSuccOrderEmb.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max Fin.castSuccOrderEmb.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hk)) ht = 0 := by
  rw [front_hom_zero s J a b k hJ ha hb hk hc]
  exact compose_zero g ht

/-- 概要：先頭面の辺を先に作用させる合成は後に作用する射と異種等号で一致する。
方針：単位の同定と両先頭対象の一致を通常順の単位則へ渡す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：最初の削除項の復元。 -/
lemma compose_front_hom_unit {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card = 2) {z : D} {q t : ℤ}
    (g : GradedHom A (s.val.obj b.castSucc) z q) (ht : k + q = t) :
    HEq (compose A g (s.val.hom (J.image Fin.castSucc) a.castSucc b.castSucc k
      (Index.image_two (Fin.castSucc_injective _).injOn hJ)
      (Index.image_min Fin.castSuccOrderEmb.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max Fin.castSuccOrderEmb.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hk)) ht) g := by
  apply compose_unit_of_heq g _ ht
  · exact (source_obj s a).trans (source_obj s b).symm
  · omega
  · refine (front_hom_unit s J a b k hJ ha hb hk hc).trans ?_
    rw [source_obj s b]

end SerrePositivity.InfinityCategories.DGNerve.PinchedHom
