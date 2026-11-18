module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Slots
public import SerrePositivity.CategoryTheory.Limits

/-!
模型。文献の定義との比較は後で
# 部分合成の挿入区間における置換の計算

概要：Berger–Moerdijk §1 の部分合成の等変性で現れる置換を入力位置で計算する。
方針：挿入分解の前・中・後の三つの区間で、同値と逆同値を展開する。
規約：入力位置は 0 始まり。arity 0 の挿入も許す。
使われ方：部分合成の等変性を全入力への合成のブロック置換と比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：内側置換は挿入区間より前の入力を固定する（Berger–Moerdijk §1）。
方針：挿入分解の左成分とその逆写像を計算する。
規約：不等式は入力位置の自然数の値について述べる。
使われ方：部分合成後にも残る前方の入力の位置を追跡する。 -/
lemma operadInnerPermutation_before (m n : ℕ) (i : Fin (m + 1))
    (τ : Equiv.Perm (Fin n)) (x : Fin (m + n)) (hx : x.val < i.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ x = x := by
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, hx, -Fin.val_fin_lt]

/-- 概要：挿入区間内では内側の置換をそのまま平行移動して適用する（Berger–Moerdijk §1）。
方針：挿入分解の右成分と逆写像を計算する。
規約：挿入区間内の入力は i+j で表す。
使われ方：連結した入力の各ブロック内の置換と同定する。 -/
lemma operadInnerPermutation_inside (m n : ℕ) (i : Fin (m + 1))
    (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ ⟨i.val + j.val, by omega⟩ =
      ⟨i.val + (τ j).val, by have := (τ j).isLt; omega⟩ := by
  have h₁ : ¬i.val + j.val < i.val := by omega
  have h₂ : i.val + j.val < i.val + n := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, h₁, h₂]

/-- 概要：内側置換は挿入区間より後の入力を固定する（Berger–Moerdijk §1）。
方針：挿入分解の後方成分を計算し、位置の加減算を整理する。
規約：arity 0 のときも後方区間は同じ式で扱う。
使われ方：部分合成の等変性で未代入の後方入力を固定する。 -/
lemma operadInnerPermutation_after (m n : ℕ) (i : Fin (m + 1))
    (τ : Equiv.Perm (Fin n)) (x : Fin (m + n)) (hx : i.val + n ≤ x.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ x = x := by
  have h₁ : ¬x.val < i.val := by omega
  have h₂ : ¬x.val < i.val + n := by omega
  have h₃ : ¬x.val + 1 - n < i.val := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, h₁, h₂, h₃, -Fin.val_fin_lt]
  omega

/-- 概要：外側置換は挿入区間を内部の順序を保って移す（Berger–Moerdijk §1）。
方針：挿入分解の内側成分で外側置換が恒等であることを使う。
規約：位置 i+j は σ(i)+j に送られる。
使われ方：後方入力の置換によって挿入区間が固定されることを示す。 -/
lemma operadOuterPermutation_inside (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (j : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ ⟨i.val + j.val, by omega⟩ =
      ⟨(σ i).val + j.val, by have := (σ i).isLt; omega⟩ := by
  have h₁ : ¬i.val + j.val < i.val := by omega
  have h₂ : i.val + j.val < i.val + n := by omega
  apply Fin.ext
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, h₁, h₂]

/-- 概要：外側置換を挿入前の残りの入力の座標で記述する（Berger–Moerdijk §1）。
方針：挿入分解とその逆写像の相殺を使う。
規約：入力は挿入位置を除いた部分型に属する。
使われ方：挿入区間外の入力を外側の置換で追跡する。 -/
lemma operadOuterPermutation_remaining (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (j : {j : Fin (m + 1) // j ≠ i}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).symm (Sum.inl j)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n (σ i)).symm
        (Sum.inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv m i σ) j)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.sumCongr_apply]
  rfl

/-- 概要：ブロック全単射は左ブロックの入力に左の全単射を適用する（Berger–Moerdijk §1）。
方針：有限直和と Fin の同値の左成分を計算する。
規約：左右の長さは固定する。
使われ方：挿入区間の置換を既存のブロック全単射と比較する。 -/
lemma blockEquiv_apply_left (a b : ℕ) (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b))
    (x : Fin a) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv σ τ (x.castAdd b) = (σ x).castAdd b := by
  change _root_.SerrePositivity.FiniteBijection.blockEquiv σ τ (finSumFinEquiv (Sum.inl x)) = _
  simp [_root_.SerrePositivity.FiniteBijection.blockEquiv]

/-- 概要：ブロック全単射は右ブロックの入力に右の全単射を適用する（Berger–Moerdijk §1）。
方針：有限直和と Fin の同値の右成分を計算する。
規約：右入力を左ブロックの長さだけ平行移動する。
使われ方：挿入区間と連結後の入力位置を比較する。 -/
lemma blockEquiv_apply_right (a b : ℕ) (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b))
    (x : Fin b) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv σ τ (x.natAdd a) = (τ x).natAdd a := by
  change _root_.SerrePositivity.FiniteBijection.blockEquiv σ τ (finSumFinEquiv (Sum.inr x)) = _
  simp [_root_.SerrePositivity.FiniteBijection.blockEquiv]

/-- 概要：最後の入力への挿入の内側置換は右ブロックの置換である（Berger–Moerdijk §1）。
方針：前方区間と挿入区間で入力を分け、両方の置換の値を比較する。
規約：arity 0 の挿入では右ブロックは空。
使われ方：最後の入力から行う全入力への合成の帰納法を始める。 -/
lemma operadInnerPermutation_last (m n : ℕ) (τ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n (Fin.last m) τ =
      _root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin m)) τ := by
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
  cases y with
  | inl y =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n (Fin.last m) τ (y.castAdd n) =
      _root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin m)) τ (y.castAdd n)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_before m n (Fin.last m) τ _ (by exact y.isLt)]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left m n (Equiv.refl (Fin m)) τ y).symm
  | inr y =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n (Fin.last m) τ (y.natAdd m) =
      _root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin m)) τ (y.natAdd m)
    have he : y.natAdd m = (⟨(Fin.last m).val + y.val, by omega⟩ : Fin (m + n)) := by
      apply Fin.ext
      rfl
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right]
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_inside]
    rfl

/-- 概要：内側置換の拡張は恒等置換を保つ（Berger–Moerdijk §1）。
方針：挿入分解による共役と直和上の恒等置換を簡約する。
規約：空の挿入区間にも適用する。
使われ方：全入力への合成の等変性の単位の場合を処理する。 -/
@[simp]
lemma operadInnerPermutation_one (m n : ℕ) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i 1 = 1 := by
  ext x
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation]

/-- 概要：内側置換の拡張は置換の積を保つ（Berger–Moerdijk §1）。
方針：挿入分解による共役の中で二つの置換を合成する。
規約：置換の積は右の置換を先に適用する。
使われ方：生成する置換についての等変性を任意の置換へ拡張する。 -/
lemma operadInnerPermutation_mul (m n : ℕ) (i : Fin (m + 1))
    (σ τ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i (σ * τ) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i σ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ := by
  ext x
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation, Equiv.Perm.mul_def, Equiv.trans_apply]
  simp

/-- 概要：内側置換は外側置換による挿入区間の移動と可換である（Berger–Moerdijk §1）。
方針：挿入分解の直和上で、左右の成分に働く置換の可換性を使う。
規約：外側の置換の後では挿入位置を σ(i) とする。
使われ方：内側と外側の同時置換を全入力への合成へ運ぶ。 -/
lemma operadInnerPermutation_outer (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n (σ i) τ) := by
  ext x
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rcases (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i) x with j | j <;> rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
