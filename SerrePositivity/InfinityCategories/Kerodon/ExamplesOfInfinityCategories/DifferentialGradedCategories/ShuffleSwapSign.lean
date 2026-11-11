module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleSwap

/-!
# 隣接する混合ステップの交換による shuffle 符号の反転

概要：水平・垂直の順を交換すると逆転数が一つ増えることを計数する。
方針：交換した水平ステップだけの寄与が一つ増え、他の前半ステップ数は変わらない。
規約：KST Construction A.5 の標準 shuffle、逆転数は垂直が水平に先行する対の数。
使われ方：混合境界項の同じ実写像を逆符号で相殺する。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory

/-- 概要：交換後の水平ステップへの所属は交換前の逆像への所属。
方針：置換による有限集合の像と、交換の対合性を使う。
規約：KST A.5。使われ方：交換した二つのステップの種類の確認。 -/
lemma ShuffleIndex.mem_swapSteps {p n : ℕ} (s : ShuffleIndex p n) (a b x : Fin n) :
    x ∈ (s.swapSteps a b).val ↔ Equiv.swap a b x ∈ s.val := by
  change x ∈ s.val.map (Equiv.swap a b).toEmbedding ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    subst x
    change Equiv.swap a b (Equiv.swap a b y) ∈ s.val
    have he : Equiv.swap a b (Equiv.swap a b y) = y := (Equiv.swap a b).symm_apply_apply y
    rw [he]
    exact hy
  · intro hx
    refine ⟨Equiv.swap a b x, hx, ?_⟩
    exact (Equiv.swap a b).symm_apply_apply x

/-- 概要：二回の交換は元の shuffle に戻る。
方針：全てのステップの所属と置換の対合性を比較する。
規約：KST A.5。使われ方：混合境界項の対合の構成。 -/
lemma ShuffleIndex.swapSteps_swapSteps {p n : ℕ} (s : ShuffleIndex p n) (a b : Fin n) :
    (s.swapSteps a b).swapSteps a b = s := by
  apply Subtype.ext
  ext x
  rw [ShuffleIndex.mem_swapSteps, ShuffleIndex.mem_swapSteps]
  have he : Equiv.swap a b (Equiv.swap a b x) = x := (Equiv.swap a b).symm_apply_apply x
  rw [he]

/-- 概要：逆転数は水平ステップの直前の垂直座標の和。
方針：二つの定義の前半ステップ集合を評価する。
規約：KST A.5、全ステップ数 p+q=n。
使われ方：交換による逆転数の変化を格子路の座標で計数する。 -/
lemma ShuffleIndex.inversions_eq_right {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    s.inversions = ∑ j ∈ s.val, ((s.right h).toOrderHom j.castSucc : ℕ) := rfl

/-- 概要：水平・垂直の順を垂直・水平に交換すると逆転数は一つ増える。
方針：水平ステップの和を交換の置換で移し、交換した一つの水平ステップの寄与を比較する。
規約：KST A.5、a=k は水平、b=k+1 は垂直。
使われ方：標準 shuffle の混合境界項の交代符号。 -/
lemma ShuffleIndex.swapSteps_inversions {p q n : ℕ} (s : ShuffleIndex p (n + 2))
    (h : p + q = n + 2) (k : Fin (n + 1))
    (ha : k.castSucc ∈ s.val) (hb : k.succ ∉ s.val) :
    (s.swapSteps k.castSucc k.succ).inversions = s.inversions + 1 := by
  let t := s.swapSteps k.castSucc k.succ
  have he : ∀ j ∈ s.val,
      ((t.right h).toOrderHom (Equiv.swap k.castSucc k.succ j).castSucc : ℕ) =
        ((s.right h).toOrderHom j.castSucc : ℕ) + if j = k.castSucc then 1 else 0 := by
    intro j hj
    by_cases hja : j = k.castSucc
    · subst j
      rw [Equiv.swap_apply_left, ite_eq_left rfl]
      have hna : k.castSucc ∉ t.val := by
        rw [ShuffleIndex.mem_swapSteps, Equiv.swap_apply_left]
        exact hb
      have hstep := t.right_step h k.castSucc
      rw [ite_eq_left hna] at hstep
      have hpre := s.swapSteps_right_prefix h k k.castSucc.castSucc
        (by change (k : ℕ) ≠ (k : ℕ) + 1; omega)
      rw [hpre] at hstep
      exact hstep
    · have hjb : j ≠ k.succ := fun he ↦ hb (he ▸ hj)
      rw [Equiv.swap_apply_of_ne_of_ne hja hjb, ite_eq_right hja, add_zero]
      apply s.swapSteps_right_prefix h k j.castSucc
      intro he
      apply hjb
      exact Fin.ext he
  rw [t.inversions_eq_right h, s.inversions_eq_right h]
  change (∑ j ∈ s.val.map (Equiv.swap k.castSucc k.succ).toEmbedding,
      ((t.right h).toOrderHom j.castSucc : ℕ)) = _
  rw [Finset.sum_map]
  calc
    _ = ∑ j ∈ s.val, (((s.right h).toOrderHom j.castSucc : ℕ) +
        if j = k.castSucc then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact he j hj
    _ = _ := by simp [Finset.sum_add_distrib, ha]

/-- 概要：隣接する混合ステップを交換すると標準 shuffle の符号が反転する。
方針：逆転数が一つ増えることを (−1) の冪に適用する。
規約：KST Construction A.5、水平・垂直から垂直・水平への交換。
使われ方：同じ混合面の実写像の二項を相殺する。 -/
lemma ShuffleIndex.swapSteps_sign {p q n : ℕ} (s : ShuffleIndex p (n + 2))
    (h : p + q = n + 2) (k : Fin (n + 1))
    (ha : k.castSucc ∈ s.val) (hb : k.succ ∉ s.val) :
    (-1 : ℤ) ^ (s.swapSteps k.castSucc k.succ).inversions = -((-1 : ℤ) ^ s.inversions) := by
  rw [s.swapSteps_inversions h k ha hb]
  simp [pow_succ]

/-- 概要：隣接する水平・垂直ステップを交換した二つの混合境界項は相殺する。
方針：実テンソル写像の一致と逆転数による符号の反転を合成する。
規約：KST Construction A.5 の標準 shuffle、全体の境界の面の符号を掛ける前。
使われ方：shuffle の実鎖写像性の混合面の部分。 -/
lemma shuffleSwapMixedFace_cancel
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) {p q n : ℕ} (s : ShuffleIndex p (n + 2))
    (h : p + q = n + 2) (k : Fin (n + 1))
    (ha : k.castSucc ∈ s.val) (hb : k.succ ∉ s.val) :
    (-1 : ℤ) ^ (s.swapSteps k.castSucc k.succ).inversions •
      (integerTensorMap (C.map (s.swapSteps k.castSucc k.succ).left.op)
          (D.map ((s.swapSteps k.castSucc k.succ).right h).op) ≫
        integerTensorMap (C.δ k.succ.castSucc) (D.δ k.succ.castSucc)) +
    (-1 : ℤ) ^ s.inversions •
      (integerTensorMap (C.map s.left.op) (D.map (s.right h).op) ≫
        integerTensorMap (C.δ k.succ.castSucc) (D.δ k.succ.castSucc)) = 0 := by
  rw [s.swapSteps_sign h k ha hb, shuffleSwapMixedFace_map C D s h k]
  simp

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

