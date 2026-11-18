module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations

/-!
模型。文献の定義との比較は後で
# 指定入力より前の置換と部分合成

概要：Berger–Moerdijk §1 の反復合成で、最後に代入する位置より前の置換を追跡する。
方針：前半のブロック置換を arity の括弧に合わせ、挿入前後の三つの区間で比較する。
規約：前半 a 入力を置換し、その後の挿入区間と未代入の尾 b 入力を保つ。
使われ方：末尾以外の隣接交換に関する部分合成の外側等変性を記述する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：前半 a 入力を置換し後方の b+l 入力を固定する（Berger–Moerdijk §1）。
方針：前半の置換と後半の恒等置換のブロック和を arity の括弧に合わせて移す。
規約：対象の arity は (a+b)+l。
使われ方：l=1 で挿入前、一般の l で挿入後の外側置換を表す。 -/
def operadPrefixPermutation (a b l : ℕ) (σ : Equiv.Perm (Fin a)) :
    Equiv.Perm (Fin ((a + b) + l)) :=
  (finCongr (Nat.add_assoc a b l).symm).permCongr
    (_root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin (b + l))))

/-- 概要：前半の置換を前半と後半の括弧へ戻すと通常のブロック置換となる（Berger–Moerdijk §1）。
方針：長さの移送の逆同値による共役を相殺する。
規約：移送後の arity は a+(b+l)。
使われ方：部分合成後の arity の移送と置換作用を比較する。 -/
lemma operadPrefixPermutation_index (a b l : ℕ) (σ : Equiv.Perm (Fin a)) :
    (finCongr (Nat.add_assoc a b l)).permCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b l σ) =
      _root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin (b + l))) := by
  have he : finCongr (Nat.add_assoc a b l).symm = (finCongr (Nat.add_assoc a b l)).symm := by
    apply Equiv.ext
    intro x
    apply Fin.ext
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation, he, ← Equiv.permCongr_symm]
  exact (finCongr (Nat.add_assoc a b l)).permCongr.apply_symm_apply _

private lemma finCongr_prefix_perm_val {r s : ℕ} (h : r = s)
    (σ : Equiv.Perm (Fin r)) (x : Fin s) :
    (((finCongr h).permCongr σ) x).val = (σ ⟨x.val, by omega⟩).val := by
  subst s
  rfl

/-- 概要：前半のブロックの各入力には指定した置換が作用する（Berger–Moerdijk §1）。
方針：ブロック全単射の左側の計算と arity の移送の値の不変性を使う。
規約：前半の位置は j.val で指定する。
使われ方：挿入区間より前の入力を追跡する。 -/
lemma operadPrefixPermutation_prefix (a b l : ℕ) (σ : Equiv.Perm (Fin a)) (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b l σ ⟨j.val, by omega⟩ =
      ⟨(σ j).val, by have := (σ j).isLt; omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_prefix_perm_val]
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin (b + l)))
    (j.castAdd (b + l))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left]
  rfl

/-- 概要：前半の置換は後方の全ての入力を固定する（Berger–Moerdijk §1）。
方針：ブロック全単射の右側の計算を使う。
規約：後方の位置は a+j.val で指定する。
使われ方：挿入位置と代入した入力、未代入の尾を固定する。 -/
lemma operadPrefixPermutation_suffix (a b l : ℕ) (σ : Equiv.Perm (Fin a)) (j : Fin (b + l)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b l σ ⟨a + j.val, by omega⟩ = ⟨a + j.val, by omega⟩ := by
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_prefix_perm_val]
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin (b + l))) (j.natAdd a)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right]
  rfl

/-- 概要：前半の置換は次に代入する位置 a を固定する（Berger–Moerdijk §1）。
方針：後方ブロックの最初の位置の固定を使う。
規約：挿入前の区間の長さは 1。
使われ方：部分合成の外側等変性の挿入位置を変えずに適用する。 -/
lemma operadPrefixPermutation_slot (a b : ℕ) (σ : Equiv.Perm (Fin a)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ ⟨a, by omega⟩ = ⟨a, by omega⟩ := by
  simpa only [Fin.val_zero, Nat.add_zero] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_suffix a b 1 σ (0 : Fin (b + 1))

/-- 概要：前半の置換を代入後へ延長すると前半には同じ置換が作用する（Berger–Moerdijk §1）。
方針：挿入分解の前方成分と置換後の前方成分を評価する。
規約：位置 a に l 入力の演算を代入する。
使われ方：部分合成後の置換を前半のブロック置換へ同定する。 -/
lemma operadOuterPermutation_prefix_before (a b l : ℕ) (σ : Equiv.Perm (Fin a))
    (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ)
      ⟨j.val, by omega⟩ = ⟨(σ j).val, by have := (σ j).isLt; omega⟩ := by
  have hj : j.val < a := j.isLt
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_prefix a b 1 σ j
  have hs : (σ j).val < a := (σ j).isLt
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_slot, hp, hj, hs, -Fin.val_fin_lt]

/-- 概要：前半の置換を代入後へ延長しても代入した区間の内部を固定する（Berger–Moerdijk §1）。
方針：外側置換の挿入区間での値と挿入位置の固定を使う。
規約：挿入後の位置は a+j.val。
使われ方：代入後の右ブロックの前方の入力を固定する。 -/
lemma operadOuterPermutation_prefix_inside (a b l : ℕ) (σ : Equiv.Perm (Fin a))
    (j : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ)
      ⟨a + j.val, by omega⟩ = ⟨a + j.val, by omega⟩ := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_slot] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_inside (a + b) l ⟨a, by omega⟩
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ) j

/-- 概要：前半の置換を代入後へ延長しても元の未代入の尾を固定する（Berger–Moerdijk §1）。
方針：挿入前の後方入力を復元し、前半の置換がそれを固定することを使う。
規約：挿入後の尾の位置は a+l+j.val。
使われ方：代入後の右ブロックの後方の入力を固定する。 -/
lemma operadOuterPermutation_prefix_after (a b l : ℕ) (σ : Equiv.Perm (Fin a))
    (j : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ)
      ⟨a + l + j.val, by omega⟩ = ⟨a + l + j.val, by omega⟩ := by
  have h₁ : ¬a + l + j.val < a := by omega
  have h₂ : ¬a + l + j.val < a + l := by omega
  have he : a + l + j.val + 1 - l = a + 1 + j.val := by omega
  have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ
      (⟨a + 1 + j.val, by omega⟩ : Fin (a + b + 1)) = ⟨a + 1 + j.val, by omega⟩ := by
    have hpoint : (⟨a + 1 + j.val, by omega⟩ : Fin (a + b + 1)) =
        ⟨a + j.succ.val, by omega⟩ := by apply Fin.ext; dsimp; omega
    rw [hpoint]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_suffix a b 1 σ j.succ
  have hρ : ¬a + 1 + j.val < a := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_slot, h₁, h₂, he, hp, hρ, -Fin.val_fin_lt]
  omega

/-- 概要：代入後の前半の置換は挿入区間と元の尾をまとめた右ブロックを固定する（Berger–Moerdijk §1）。
方針：右ブロックを挿入した区間と元の尾に場合分けする。
規約：l=0 のときは右ブロック全体が元の尾となる。
使われ方：代入後の置換を二ブロックの置換として比較する。 -/
lemma operadOuterPermutation_prefix_suffix (a b l : ℕ) (σ : Equiv.Perm (Fin a))
    (j : Fin (b + l)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ)
      ⟨a + j.val, by omega⟩ = ⟨a + j.val, by omega⟩ := by
  by_cases hj : j.val < l
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_prefix_inside a b l σ ⟨j.val, hj⟩
  · let t : Fin b := ⟨j.val - l, by omega⟩
    have he : (⟨a + j.val, by omega⟩ : Fin (a + b + l)) =
        ⟨a + l + t.val, by omega⟩ := by apply Fin.ext; dsimp [t]; omega
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_prefix_after a b l σ t

/-- 概要：挿入前の前半の置換を代入後へ延長すると同じ前半のブロック置換となる（Berger–Moerdijk §1）。
方針：前半と右ブロックに入力を分けて値を比較する。
規約：代入した区間と元の未代入入力の内部の順序を保つ。
使われ方：部分合成の外側等変性の出力の置換を反復合成の帰納段階へ渡す。 -/
lemma operadOuterPermutation_prefix (a b l : ℕ) (σ : Equiv.Perm (Fin a)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation (a + b) l ⟨a, by omega⟩ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b l σ := by
  let h := Nat.add_assoc a b l
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (finCongr h.symm).surjective x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
  cases y with
  | inl j =>
    have he : finCongr h.symm (finSumFinEquiv (Sum.inl j)) =
        (⟨j.val, by omega⟩ : Fin (a + b + l)) := by apply Fin.ext; rfl
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_prefix_before, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_prefix]
  | inr j =>
    have he : finCongr h.symm (finSumFinEquiv (Sum.inr j)) =
        (⟨a + j.val, by omega⟩ : Fin (a + b + l)) := by apply Fin.ext; rfl
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_prefix_suffix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_suffix]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
