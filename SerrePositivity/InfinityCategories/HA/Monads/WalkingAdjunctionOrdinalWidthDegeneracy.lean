module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPrecomp
public import SerrePositivity.InfinityCategories.HA.Monads.NerveDegeneracyEdges

/-!
概要：元のnerveの全実退化は有限順序の幅を保つ。
方針：重なる一辺の変化量は0、残りの実辺は元の全実辺と一対一に対応する。
規約：全次数と全退化位置、元の実関手の作用を使う。
使われ方：Riehl–Verity Proposition 4.2.15、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの退化の法則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：退化で重なる辺以外の辺は、元の同じ隣接二点へ戻る。
方針：重なる位置の前後に分け、有限添字の値を計算する。
規約：全退化位置。使われ方：Riehl–Verity §4.2の退化と幅の照合。 -/
lemma finPredAbove_other_edge {n : ℕ} (j : Fin (n + 1)) (i : Fin n) :
    j.predAbove (j.succAbove i).castSucc = i.castSucc ∧
      j.predAbove (j.succAbove i).succ = i.succ := by
  by_cases h : i.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    constructor
    · exact Fin.predAbove_castSucc_of_le _ _ (le_of_lt h)
    · rw [Fin.predAbove_succ_of_lt _ _ h]
      rfl
  · have hj : j ≤ i.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hj]
    constructor
    · rw [Fin.predAbove_castSucc_of_lt _ _ (lt_of_le_of_lt hj (Fin.castSucc_lt_succ (i := i)))]
      apply Fin.ext
      change i.val + 1 - 1 = i.val
      omega
    · exact Fin.predAbove_succ_of_le _ _ (le_trans hj (Fin.castSucc_le_succ i))

/-- 概要：実退化の重なる辺以外の変化量は、元の対応する実辺の変化量に等しい。
方針：実有限添字の両端を戻し、同じ実射へ輸送する。
規約：元のnerveの作用。使われ方：Riehl–Verity §4.2の全実辺の和の保存。 -/
lemma walkingAdjunctionDegeneracy_other_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) (i : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom (((nerve (walkingAdjunctionHom X Y)).σ j H).map
      (homOfLE (Fin.castSucc_le_succ (j.succAbove i))))) =
    ordinalMapVariation (walkingAdjunctionOrderHom (H.map
      (homOfLE (Fin.castSucc_le_succ i)))) := by
  let P := (SimplexCategory.σ j).toOrderHom.monotone.functor
  have hp := finPredAbove_other_edge j i
  have hh {a b : Fin (n + 2)} {a' b' : Fin (n + 1)}
      (ha : P.obj a = a') (hb : P.obj b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
      HEq (H.map (P.map (homOfLE hab))) (H.map (homOfLE hab')) := by
    subst a'
    subst b'
    rfl
  exact walkingAdjunctionMapVariation_heq (congrArg H.obj hp.1) (congrArg H.obj hp.2)
    _ _ (hh hp.1 hp.2 _ _)

/-- 概要：実退化の重なる辺の変化量は0。
方針：元のnerveでの実辺の同型性を変化量0へ移す。
規約：対象の等式を新しい仮定にしない。使われ方：Riehl–Verity §4.2の退化の幅。 -/
lemma walkingAdjunctionDegeneracy_collapsed_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) :
    ordinalMapVariation (walkingAdjunctionOrderHom (((nerve (walkingAdjunctionHom X Y)).σ j H).map
      (homOfLE (Fin.castSucc_le_succ j)))) = 0 :=
  (walkingAdjunctionMapVariation_zero_iff_isIso _).mpr (nerve_degeneracy_edge_isIso H j)

/-- 概要：実退化は全実辺の変化量の和を保つ。
方針：有限和を重なる辺とそれ以外へ分け、実辺ごとの計算を使う。
規約：次数0も含む。使われ方：Riehl–Verity §4.2の幅の保存。 -/
lemma walkingAdjunctionDegeneracy_variation_sum {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) :
    (∑ i : Fin (n + 1), ordinalMapVariation (walkingAdjunctionOrderHom
      (((nerve (walkingAdjunctionHom X Y)).σ j H).map
        (homOfLE (Fin.castSucc_le_succ i))))) =
    ∑ i : Fin n, ordinalMapVariation (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ i)))) := by
  rw [Fin.sum_univ_succAbove _ j, walkingAdjunctionDegeneracy_collapsed_variation, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  exact walkingAdjunctionDegeneracy_other_variation H j i

/-- 概要：実退化は有限順序の幅を保つ。
方針：両端の実対象は変わらず、全実辺の変化量の和も変わらないことを使う。
規約：全実退化。使われ方：Riehl–Verity Proposition 4.2.15の実非退化表示への還元。 -/
lemma walkingAdjunctionOrdinalWidth_degeneracy {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (j : Fin (n + 1)) :
    walkingAdjunctionOrdinalWidth ((nerve (walkingAdjunctionHom X Y)).σ j H) =
      walkingAdjunctionOrdinalWidth H := by
  unfold walkingAdjunctionOrdinalWidth
  rw [walkingAdjunctionDegeneracy_variation_sum]
  have h0 : ((nerve (walkingAdjunctionHom X Y)).σ j H).obj 0 = H.obj 0 := by
    change H.obj (j.predAbove 0) = H.obj 0
    rw [Fin.predAbove_right_zero]
  have hn : ((nerve (walkingAdjunctionHom X Y)).σ j H).obj (Fin.last (n + 1)) =
      H.obj (Fin.last n) := by
    change H.obj (j.predAbove (Fin.last (n + 1))) = H.obj (Fin.last n)
    rw [Fin.predAbove_right_last]
  rw [h0, hn]

end SerrePositivity.InfinityCategories.HA.Monads
