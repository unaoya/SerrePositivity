module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations

/-!
模型。文献の定義との比較は後で
# 未代入の後方入力の置換

概要：Berger–Moerdijk §1 の等変性を、先頭の入力への反復代入に適用するための置換を構成する。
方針：前方を固定するブロック置換を、部分合成の arity の括弧付けへ移送する。
規約：指定入力の位置は a、未代入の後方入力は b 個。
使われ方：全入力への合成の等変性の帰納法で、未処理の入力の位置を追跡する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：前方 a+1 個の入力を固定し後方 b 個の入力を置換する（Berger–Moerdijk §1）。
方針：既存のブロック置換を arity の等式で移送する。
規約：対象 arity は部分合成の定義に合わせて a+b+1 とする。
使われ方：位置 a への代入後に残る後方置換を計算する。 -/
def operadTailPermutation (a b : ℕ) (ρ : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (a + b + 1)) :=
  (finCongr (by omega : (a + 1) + b = a + b + 1)).permCongr
    (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin (a + 1))) ρ)

private lemma finCongr_permCongr_val {r s : ℕ} (h : r = s) (σ : Equiv.Perm (Fin r))
    (x : Fin s) :
    (((finCongr h).permCongr σ) x).val = (σ ⟨x.val, by omega⟩).val := by
  subst s
  rfl

/-- 概要：後方ブロックの置換は前方の各入力を固定する（Berger–Moerdijk §1）。
方針：ブロック置換の左成分を計算し、arity の移送は入力の値を保つことを使う。
規約：位置 a 自身も前方ブロックに含む。
使われ方：部分合成の外側等変性で挿入位置が固定されることを示す。 -/
lemma operadTailPermutation_prefix (a b : ℕ) (ρ : Equiv.Perm (Fin b)) (j : Fin (a + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ ⟨j.val, by omega⟩ = ⟨j.val, by omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin (a + 1))) ρ (j.castAdd b)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left]
  rfl

/-- 概要：後方ブロックの各入力には指定した後方置換が作用する（Berger–Moerdijk §1）。
方針：ブロック置換の右成分を計算し、位置の平行移動を明示する。
規約：後方の開始位置は a+1。
使われ方：挿入前後で後方の入力の置換を比較する。 -/
lemma operadTailPermutation_suffix (a b : ℕ) (ρ : Equiv.Perm (Fin b)) (j : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ ⟨a + 1 + j.val, by omega⟩ =
      ⟨a + 1 + (ρ j).val, by have := (ρ j).isLt; omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin (a + 1))) ρ (j.natAdd (a + 1))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right]
  rfl

/-- 概要：後方ブロックの置換は次に代入する位置 a を固定する（Berger–Moerdijk §1）。
方針：前方の位置の固定則に最後の位置を適用する。
規約：挿入位置は arity a+b+1 の入力。
使われ方：全入力への合成の等変性の帰納段階で挿入位置を保つ。 -/
@[simp]
lemma operadTailPermutation_slot (a b : ℕ) (ρ : Equiv.Perm (Fin b)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ ⟨a, by omega⟩ = ⟨a, by omega⟩ :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation_prefix a b ρ (Fin.last a)

/-- 概要：後方入力の置換を挿入後へ延長しても前方入力は固定される（Berger–Moerdijk §1）。
方針：外側置換と挿入分解を前方の入力で評価する。
規約：位置 a へ l 個の入力を挿入する。
使われ方：次の帰納段階でも未処理の前方の位置を保持する。 -/
lemma operadOuterPermutation_tail_prefix (a b l : ℕ) (ρ : Equiv.Perm (Fin b))
    (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ)
      ⟨j.val, by omega⟩ = ⟨j.val, by omega⟩ := by
  have hj : j.val < a := j.isLt
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation_prefix a b ρ (⟨j.val, by omega⟩ : Fin (a + 1))
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation_slot, hp, hj, -Fin.val_fin_lt]

/-- 概要：後方入力の置換を挿入後へ延長すると挿入区間の各入力を固定する（Berger–Moerdijk §1）。
方針：挿入区間の内部の順序を保つ外側置換の計算則に、挿入位置の固定を適用する。
規約：挿入区間の開始位置は a。
使われ方：内側置換と後方置換を独立なブロックの置換として組み合わせる。 -/
lemma operadOuterPermutation_tail_inside (a b l : ℕ) (ρ : Equiv.Perm (Fin b))
    (j : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ)
      ⟨a + j.val, by omega⟩ = ⟨a + j.val, by omega⟩ := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation_slot] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_inside (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ) j

/-- 概要：後方入力の置換を挿入後へ延長すると後方の開始位置だけが変わる（Berger–Moerdijk §1）。
方針：挿入前の後方入力の位置を復元し、その置換後に挿入区間の長さだけずらす。
規約：後方区間の開始位置は挿入前の a+1 から a+l へ変わる。
使われ方：全入力への合成の再帰で残りの入力の置換を更新する。 -/
lemma operadOuterPermutation_tail_suffix (a b l : ℕ) (ρ : Equiv.Perm (Fin b))
    (j : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ)
      ⟨a + l + j.val, by omega⟩ =
        ⟨a + l + (ρ j).val, by have := (ρ j).isLt; omega⟩ := by
  have h₁ : ¬a + l + j.val < a := by omega
  have h₂ : ¬a + l + j.val < a + l := by omega
  have he : a + l + j.val + 1 - l = a + 1 + j.val := by omega
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation_suffix a b ρ j
  have hρ : ¬a + 1 + (ρ j).val < a := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation_slot, h₁, h₂, he, hp, hρ, -Fin.val_fin_lt]
  omega

/-- 概要：前方・挿入区間・後方の三つのブロックの置換（Berger–Moerdijk §1）。
方針：挿入区間の置換と後方置換を連結し、前方の恒等置換を付ける。
規約：部分合成の出力 arity a+b+l への移送を含む。
使われ方：内側と外側の等変性を次の反復代入の尾の置換として読む。 -/
def operadInsertedTailPermutation (a b l : ℕ) (τ : Equiv.Perm (Fin l))
    (ρ : Equiv.Perm (Fin b)) : Equiv.Perm (Fin (a + b + l)) :=
  (finCongr (by omega : a + (l + b) = a + b + l)).permCongr
    (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin a)) (_root_.SerrePositivity.FiniteBijection.blockEquiv τ ρ))

/-- 概要：三つのブロックの置換は前方の各入力を固定する（Berger–Moerdijk §1）。
方針：外側のブロック全単射の左成分を評価する。
規約：前方の長さは a。
使われ方：全入力への合成の次の帰納段階で前方の位置を固定する。 -/
lemma operadInsertedTailPermutation_prefix (a b l : ℕ) (τ : Equiv.Perm (Fin l))
    (ρ : Equiv.Perm (Fin b)) (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation a b l τ ρ ⟨j.val, by omega⟩ = ⟨j.val, by omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin a))
    (_root_.SerrePositivity.FiniteBijection.blockEquiv τ ρ) (j.castAdd (l + b))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left]
  rfl

/-- 概要：三つのブロックの置換は挿入区間で内側置換を適用する（Berger–Moerdijk §1）。
方針：二重のブロック全単射の右、左の成分を評価する。
規約：挿入区間の開始位置は a。
使われ方：部分合成の内側等変性と次の尾の置換を比較する。 -/
lemma operadInsertedTailPermutation_inside (a b l : ℕ) (τ : Equiv.Perm (Fin l))
    (ρ : Equiv.Perm (Fin b)) (j : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation a b l τ ρ ⟨a + j.val, by omega⟩ =
      ⟨a + (τ j).val, by have := (τ j).isLt; omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin a))
    (_root_.SerrePositivity.FiniteBijection.blockEquiv τ ρ) ((j.castAdd b).natAdd a)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left]
  rfl

/-- 概要：三つのブロックの置換は後方区間で後方置換を適用する（Berger–Moerdijk §1）。
方針：二重のブロック全単射の右成分を二回評価する。
規約：後方区間の開始位置は a+l。
使われ方：全入力への合成の再帰で後方置換を引き継ぐ。 -/
lemma operadInsertedTailPermutation_suffix (a b l : ℕ) (τ : Equiv.Perm (Fin l))
    (ρ : Equiv.Perm (Fin b)) (j : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation a b l τ ρ ⟨a + l + j.val, by omega⟩ =
      ⟨a + l + (ρ j).val, by have := (ρ j).isLt; omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
  have he : (⟨a + l + j.val, by omega⟩ : Fin (a + (l + b))) =
      (j.natAdd l).natAdd a := by apply Fin.ext; dsimp; omega
  rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right]
  dsimp
  omega

/-- 概要：挿入区間の内側置換と後方の外側置換は三つのブロックの置換に一致する（Berger–Moerdijk §1）。
方針：前方・挿入区間・後方に入力を分け、それぞれの置換の計算則を適用する。
規約：内側置換の後に、挿入位置を固定する外側置換を適用する。
使われ方：部分合成の等変性を全入力への合成の等変性の帰納法につなぐ。 -/
lemma operadInnerPermutation_tail_outer (a b l : ℕ) (τ : Equiv.Perm (Fin l))
    (ρ : Equiv.Perm (Fin b)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation (a + b) l ⟨a, by omega⟩ τ).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailPermutation a b ρ)) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation a b l τ ρ := by
  ext x
  simp only [Equiv.trans_apply]
  by_cases h₁ : x.val < a
  · let j : Fin a := ⟨x.val, h₁⟩
    have he : x = (⟨j.val, by omega⟩ : Fin (a + b + l)) := by rfl
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_before _ _ _ _ _ (by exact h₁),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_tail_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation_prefix]
  · by_cases h₂ : x.val < a + l
    · let j : Fin l := ⟨x.val - a, by omega⟩
      have he : x = (⟨a + j.val, by omega⟩ : Fin (a + b + l)) := by
        apply Fin.ext; dsimp [j]; omega
      rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_inside, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_tail_inside,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation_inside]
    · let j : Fin b := ⟨x.val - (a + l), by omega⟩
      have he : x = (⟨a + l + j.val, by omega⟩ : Fin (a + b + l)) := by
        apply Fin.ext; dsimp [j]; omega
      rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_after _ _ _ _ _ (by dsimp; omega),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_tail_suffix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation_suffix]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
