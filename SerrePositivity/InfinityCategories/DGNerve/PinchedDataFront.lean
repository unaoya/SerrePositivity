module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedData

/-! # 方程式を課す前の右 pinched データの先頭成分

概要：先頭面の等式だけから単位・零の計算を取り出す。
方針：データの等式を成分の異種等号へ写し、定値面の計算を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：逆構成の方程式の線形化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：等しい単体データの同じ成分は異種等号で一致する。
方針：データの等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：方程式を仮定しない先頭面の成分の比較。 -/
lemma SimplexData.data_hom_heq_of_eq {n : ℕ} {s t : SimplexData A D n} (hst : s = t)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq (s.hom J a b k hJ ha hb hk) (t.hom J a b k hJ ha hb hk) := by
  subst t
  rfl

namespace PinchedHom.Data

variable {x y : D}

/-- 概要：先頭頂点の像の成分は定値面の同じ成分と異種等号で一致する。
方針：定値面の等式を成分で評価し、先頭面の単射分岐で計算する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：先頭面の全成分の同定。 -/
lemma front_hom_heq {n : ℕ} (s : Data A D x y n)
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
  have he := SimplexData.data_hom_heq_of_eq s.source J a b k hJ ha hb hk
  change HEq ((s.val.pullback Fin.castSuccOrderEmb.toOrderHom).hom
    J a b k hJ ha hb hk) _ at he
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ (Fin.castSucc_injective _).injOn] at he
  exact he


/-- 概要：先頭埋め込みの像に等しい集合の成分は、定値面の対応する成分と異種等号で一致する。
方針：集合の等式で添字を比較し、先頭面の成分の比較へ帰着する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：切断集合の証明引数を保持した成分の移送。 -/
lemma front_hom_heq_of_image {n : ℕ} (s : Data A D x y n)
    (I : Finset (Fin (n + 2))) (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a.castSucc = I.min' (Index.nonempty hI))
    (hb : b.castSucc = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hJ : 2 ≤ J.card) (haJ : a = J.min' (Index.nonempty hJ))
    (hbJ : b = J.max' (Index.nonempty hJ)) (hIJ : I = J.image Fin.castSucc) :
    HEq (s.val.hom I a.castSucc b.castSucc k hI ha hb hk)
      ((InfinityCategories.PinchedHom.constant (X := dgNerve A D) (Simplex.vertex x) n).hom
        J a b k hJ haJ hbJ (by
          rw [hIJ, Finset.card_image_of_injective _ (Fin.castSucc_injective _)] at hk
          exact hk)) := by
  have hkJ : k = 2 - (J.card : ℤ) := by
    rw [hIJ, Finset.card_image_of_injective _ (Fin.castSucc_injective _)] at hk
    exact hk
  have he := s.val.hom_heq_of_indices I (J.image Fin.castSucc)
    a.castSucc b.castSucc a.castSucc b.castSucc k hI ha hb hk
    (Index.image_two (Fin.castSucc_injective _).injOn hJ)
    (Index.image_min Fin.castSuccOrderEmb.monotone (by rw [haJ]; exact J.isLeast_min' _) _)
    (Index.image_max Fin.castSuccOrderEmb.monotone (by rw [hbJ]; exact J.isGreatest_max' _) _)
    (by rw [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]; exact hkJ) hIJ rfl rfl
  exact he.trans (front_hom_heq s J a b k hJ haJ hbJ hkJ)


/-- 概要：先頭埋め込みの像に等しい高次集合の成分は零。
方針：添字を保持した定値面との比較と、定値単体の高次成分の零を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：左右切断の合成の消去。 -/
lemma front_hom_zero_of_image {n : ℕ} (s : Data A D x y n)
    (I : Finset (Fin (n + 2))) (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a.castSucc = I.min' (Index.nonempty hI))
    (hb : b.castSucc = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hJ : 2 ≤ J.card) (haJ : a = J.min' (Index.nonempty hJ))
    (hbJ : b = J.max' (Index.nonempty hJ)) (hIJ : I = J.image Fin.castSucc) (hc : J.card ≠ 2) :
    s.val.hom I a.castSucc b.castSucc k hI ha hb hk = 0 := by
  have he := front_hom_heq_of_image s I J a b k hI ha hb hk hJ haJ hbJ hIJ
  rw [constant_hom_zero _ _ _ _ _ _ _ _ _ hc] at he
  have hz : HEq (0 : GradedHom A x x k)
      (0 : GradedHom A (s.val.obj a.castSucc) (s.val.obj b.castSucc) k) := by
    rw [source_obj s a, source_obj s b]
  exact eq_of_heq (he.trans hz)


/-- 概要：先頭埋め込みの二点集合の像に等しい集合の成分は単位。
方針：添字を保持した定値面との比較と、定値単体の辺の単位を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：二番目の点での切断合成。 -/
lemma front_hom_unit_of_image {n : ℕ} (s : Data A D x y n)
    (I : Finset (Fin (n + 2))) (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a.castSucc = I.min' (Index.nonempty hI))
    (hb : b.castSucc = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hJ : 2 ≤ J.card) (haJ : a = J.min' (Index.nonempty hJ))
    (hbJ : b = J.max' (Index.nonempty hJ)) (hIJ : I = J.image Fin.castSucc) (hc : J.card = 2) :
    HEq (s.val.hom I a.castSucc b.castSucc k hI ha hb hk) (unitElement A x).val :=
  (front_hom_heq_of_image s I J a b k hI ha hb hk hJ haJ hbJ hIJ).trans
    (constant_hom_unit _ _ _ _ _ _ _ _ _ hc)


end PinchedHom.Data

end SerrePositivity.InfinityCategories.DGNerve
