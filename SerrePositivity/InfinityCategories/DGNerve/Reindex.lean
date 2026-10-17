module
public import SerrePositivity.InfinityCategories.DGNerve.Simplex

/-! # dg nerve の添字の引き戻し

概要：単調写像に沿って、頂点と斉次成分のデータを引き戻す。
方針：部分集合上単射なら像で評価し、潰れた辺では単位、それ以外では零を使う。
規約：HA Construction 1.3.1.6。使われ方：単体的構造のデータ部分。
このファイルのデータの構成だけでは単体の方程式の保存を主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：単調写像による頂点と斉次成分の引き戻し。
方針：像の濃度・端点の補題を使い、非単射の辺には dg 単位を与える。
規約：HA Construction 1.3.1.6 の三分岐。
使われ方：単体の方程式の保存を証明した後の単体的構造の定義。 -/
def pullback {m n : ℕ} (s : SimplexData A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) : SimplexData A D m where
  obj i := s.obj (α i)
  hom J a b k hJ ha hb hk := by
    have hamin : IsLeast (J : Set (Fin (m + 1))) a := by
      rw [ha]; exact J.isLeast_min' _
    have hbmax : IsGreatest (J : Set (Fin (m + 1))) b := by
      rw [hb]; exact J.isGreatest_max' _
    by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
    · exact s.hom (J.image α) (α a) (α b) k (Index.image_two hi hJ)
        (Index.image_min α.monotone hamin _) (Index.image_max α.monotone hbmax _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk)
    · by_cases hc : J.card = 2
      · have hab := Index.collapse_two hi hc hamin hbmax
        have hk' : k = 0 := by omega
        subst hk'
        change GradedHom A (s.obj (α a)) (s.obj (α b)) 0
        rw [hab]
        exact (unitElement A (s.obj (α b))).val
      · exact 0

/-- 概要：単射の分岐では引き戻した成分は像の成分である。
方針：定義の三分岐の第一分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：単体の方程式の保存の単射の場合。 -/
lemma pullback_hom_of_inj {m n : ℕ} (s : SimplexData A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ)) (hb : b = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    (s.pullback α).hom J a b k hJ ha hb hk =
      s.hom (J.image α) (α a) (α b) k (Index.image_two hi hJ)
        (Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
        (Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  simp only [pullback, dite_eq_left hi]

/-- 概要：恒等写像に沿うデータの引き戻しは元のデータ。
方針：全ての部分集合上で単射の分岐を取り、像が元の集合に戻ることを使う。
規約：HA Construction 1.3.1.6。使われ方：単体的恒等写像の法則。 -/
lemma pullback_id {n : ℕ} (s : SimplexData A D n) : s.pullback (OrderHom.id) = s := by
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext J a b k hJ ha hb hk
    simp [pullback]
    rfl

/-- 概要：データの引き戻しは単調写像の合成に対して反変。
方針：最初の写像の単射性と像上の次の写像の単射性で場合分けする。
規約：HA Construction 1.3.1.6。使われ方：単体的合成の法則のデータ部分。 -/
lemma pullback_comp {l m n : ℕ} (s : SimplexData A D n)
    (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (m + 1) →o Fin (n + 1)) :
    (s.pullback β).pullback α = s.pullback (β.comp α) := by
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext J a b k hJ ha hb hk
    by_cases hi : Set.InjOn α (J : Set (Fin (l + 1)))
    · have hiff : Set.InjOn (β.comp α) (J : Set (Fin (l + 1))) ↔
          Set.InjOn β ((J.image α) : Set (Fin (m + 1))) := by
        simpa only [Finset.coe_image, OrderHom.comp_coe] using hi.comp_iff (g := β)
      by_cases hiβ : Set.InjOn β ((J.image α) : Set (Fin (m + 1)))
      · simp only [pullback, dite_eq_left hi, dite_eq_left hiβ, dite_eq_left (hiff.mpr hiβ),
          Finset.image_image]
        rfl
      · have hnot := mt hiff.mp hiβ
        simp only [pullback, dite_eq_left hi, dite_eq_right hiβ, dite_eq_right hnot,
          Finset.card_image_of_injOn hi]
        by_cases hc : J.card = 2
        · have hk' : k = 0 := by omega
          subst hk'
          simp only [dite_eq_left hc]
          rfl
        · simp only [dite_eq_right hc]
    · have hnot : ¬ Set.InjOn (β.comp α) (J : Set (Fin (l + 1))) := by
        intro h
        apply hi
        intro x hx y hy hxy
        exact h hx hy (congrArg β hxy)
      simp only [pullback, dite_eq_right hi, dite_eq_right hnot]
      rfl

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
