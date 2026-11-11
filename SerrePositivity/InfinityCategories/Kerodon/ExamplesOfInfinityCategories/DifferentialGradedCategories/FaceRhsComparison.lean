module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataRhsComponents

/-! # 共通の面の等式からの右辺の比較

概要：同じ面への制限が等しい二データでは、その面に含まれる全ての右辺が一致する。
方針：集合を面の逆像へ移し、その単射の像の右辺の異種等号を使って元の添字へ戻す。
規約：HA Proposition 1.3.1.10。使われ方：左右の先頭と D 側の右辺の型付き比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：面への制限が等しい二データの、その面内の集合の右辺は異種等号で一致する。
方針：飛ばす頂点を含まない集合の面への逆像を取り、濃度と端点を像で復元する。
規約：HA Proposition 1.3.1.10。使われ方：共通面の先頭・D 側の残差を直接比較する。 -/
lemma rhs_heq_of_face_pullback_eq {n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1))
    (j : Fin (n + 2))
    (h : s.pullback j.succAboveOrderEmb.toOrderHom = t.pullback j.succAboveOrderEmb.toOrderHom)
    (I : Finset (Fin (n + 2))) (hj : j ∉ I)
    (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq (s.rhs I a b k hI ha hb hk) (t.rhs I a b k hI ha hb hk) := by
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
  have hJ : 2 ≤ J.card := by omega
  have hImage : J.image j.succAboveOrderEmb.toOrderHom = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have ha' : j.succAboveOrderEmb.toOrderHom a' = a := by
    rw [ha]
    simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min
      (f := j.succAboveOrderEmb.toOrderHom) j.succAboveOrderEmb.monotone
      (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
  have hb' : j.succAboveOrderEmb.toOrderHom b' = b := by
    rw [hb]
    simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max
      (f := j.succAboveOrderEmb.toOrderHom) j.succAboveOrderEmb.monotone
      (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_pullback_eq s t j.succAboveOrderEmb.toOrderHom
    j.succAboveOrderEmb.toOrderHom h J a' b' k hJ rfl rfl (by rw [hcard]; exact hk)
    j.succAboveOrderEmb.injective.injOn j.succAboveOrderEmb.injective.injOn
  cases ha'
  cases hb'
  simpa only [hImage] using H

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_heq_of_face_pullback_eq)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
