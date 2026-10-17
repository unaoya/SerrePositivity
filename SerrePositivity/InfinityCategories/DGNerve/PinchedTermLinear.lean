module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms

/-! # 右 pinched 方程式の各項の線形表示

概要：内部点の寄与を、削除成分と二番目の点だけに現れる最小点削除成分で表す。
方針：削除項の回収と切断合成の単位・零の計算を符号付き差にまとめる。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：全右辺の有限和の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：対象を等式で移送した二つの射の符号付き差は異種等号で一致する。
方針：対象の等式を消去し、二つの異種等号を通常の等号に直す。
規約：HA Construction 1.3.1.6。使われ方：元の単体の項と回収した線形項の比較。 -/
lemma smul_sub_heq_of_obj_eq {a b c d : D} (ha : a = c) (hb : b = d) {k : ℤ}
    (e : ℤˣ) (f g : GradedHom A a b k) (f' g' : GradedHom A c d k)
    (hf : HEq f f') (hg : HEq g g') : HEq (e • (f - g)) (e • (f' - g')) := by
  subst c
  subst d
  have hf' := eq_of_heq hf
  have hg' := eq_of_heq hg
  rw [hf', hg']

namespace PinchedHom

open scoped Simplicial

variable {x y : D}

/-- 概要：各内部先頭点の寄与は、その点の削除成分と二番目だけに残る最小点削除成分の符号付き差。
方針：削除成分の同定と、切断合成が二番目で単位、それ以外で零となる計算を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：全ての内部点の寄与の線形化。 -/
lemma term_heq_linear {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' (Index.nonempty hJ) < j) :
    HEq (s.val.toSimplexData.term (withLast J) (J.min' (Index.nonempty hJ)).castSucc
      (Fin.last (n + 1)) k (two_withLast (Index.nonempty hJ))
      (min_withLast (Index.nonempty hJ) _) (max_withLast J _) (by rw [card_withLast]; omega)
      j.castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
      (Fin.castSucc_lt_castSucc_iff.mpr haj) (Fin.castSucc_lt_last j))
      ((((J.filter (j < ·)).card : ℤ) + 1).negOnePow •
        ((toLinearData s).component (J.erase j) (k + 1) (LinearData.erase_nonempty hJ j hj)
          (by have := Finset.card_erase_add_one hj; omega) -
        if j = second J hJ then
          (toLinearData s).component (J.erase (J.min' (Index.nonempty hJ))) (k + 1)
            (LinearData.erase_nonempty hJ _ (J.min'_mem _))
            (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ)); omega)
        else 0)) := by
  rw [SimplexData.term_eq_sub_cutComposite, card_above_withLast]
  simp only [Nat.cast_add, Nat.cast_one]
  apply smul_sub_heq_of_obj_eq (source_obj s _) (target_obj s)
  · exact erasedComponent_heq_component s J hJ k hk j hj haj
  · by_cases hjs : j = second J hJ
    · subst j
      rw [ite_eq_left rfl]
      exact cutComposite_second_heq_component s J hJ k hk
    · rw [ite_eq_right hjs, cutComposite_zero_of_ne_second s J hJ k hk j hj haj hjs]
      rw [source_obj s _, target_obj s]

end PinchedHom

end SerrePositivity.InfinityCategories.DGNerve
