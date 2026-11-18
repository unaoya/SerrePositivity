module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionLabels
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

/-!
模型。文献の定義との比較は後で
# 合成語の逆構成で使う内外ラベルへの射影

概要：Berger–Fresse §1.5.9 の合成語のラベルを元の外側と内側へ戻す。
方針：既存の挿入ラベル直和分解を逆に読む。
規約：内側ラベルは外側へは指定値、外側ラベルは内側へは none。
使われ方：元の語と挿入部分語の一意な復元。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：合成ラベルを外側ラベルへ戻す（BF §1.5.9）。
方針：残る外側ラベルは元の値、挿入ラベルは指定値にする。
規約：内側 arity 零も同じ直和分解。
使われ方：合成語から元の外側語を復元する。 -/
def outerLabel {m n : ℕ} (k : Fin (m + 1)) (a : Fin (m + n)) : Fin (m + 1) :=
  match _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k a with
  | Sum.inl b => b.val
  | Sum.inr _ => k

/-- 概要：合成ラベルの内側由来の値だけを戻す（BF §1.5.9）。
方針：挿入ラベルは元の値、残る外側ラベルは none とする。
規約：filterMap により外側由来の値を除く。
使われ方：合成語から元の内側部分語列を復元する。 -/
def innerLabel {m n : ℕ} (k : Fin (m + 1)) (a : Fin (m + n)) : Option (Fin n) :=
  match _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k a with
  | Sum.inl _ => none
  | Sum.inr b => some b

/-- 概要：残る外側ラベルの外側射影は元の値（BF §1.5.9）。
方針：挿入分解の同値の往復を消す。
規約：指定値と異なるラベル。
使われ方：外側語の各文字の復元。 -/
@[simp] lemma outerLabel_remaining {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k (remainingPosition m n k a) = a.val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel, remainingPosition, Equiv.apply_symm_apply]

/-- 概要：挿入ラベルの外側射影は指定値（BF §1.5.9）。
方針：挿入分解の右成分を評価する。
規約：内側の値には依存しない。
使われ方：各非空挿入部分語を指定値の一つへ縮める。 -/
@[simp] lemma outerLabel_inserted {m n : ℕ} (k : Fin (m + 1)) (a : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k (insertedPosition m n k a) = k := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel, insertedPosition, Equiv.apply_symm_apply]

/-- 概要：残る外側ラベルの内側射影はない（BF §1.5.9）。
方針：挿入分解の左成分を評価する。
規約：外側由来の文字は filterMap で消える。
使われ方：内側部分語列の復元。 -/
@[simp] lemma innerLabel_remaining {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k (remainingPosition m n k a) = none := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel, remainingPosition, Equiv.apply_symm_apply]

/-- 概要：挿入ラベルの内側射影は元の値（BF §1.5.9）。
方針：挿入分解の同値の往復を消す。
規約：元の内側値を区別する。
使われ方：内側部分語の各文字の復元。 -/
@[simp] lemma innerLabel_inserted {m n : ℕ} (k : Fin (m + 1)) (a : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k (insertedPosition m n k a) = some a := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel, insertedPosition, Equiv.apply_symm_apply]

/-- 概要：挿入部分語の外側射影は同じ長さの指定値の反復（BF §1.5.9）。
方針：部分語の各挿入ラベルを指定値へ戻す。
規約：空語でも成立。
使われ方：外側復元で非空部分語を一つの指定値へ縮める。 -/
lemma outerLabel_map_inserted {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin n)) :
    (xs.map (insertedPosition m n k)).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k) = List.replicate xs.length k := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel_inserted, List.length_cons, List.replicate_succ, ih]

/-- 概要：挿入部分語の内側射影は元の部分語（BF §1.5.9）。
方針：元の各挿入ラベルを some の値へ戻す。
規約：空部分語も許す。
使われ方：合成語から元の全内側部分語列を取り出す。 -/
lemma innerLabel_filterMap_inserted {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin n)) :
    (xs.map (insertedPosition m n k)).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, List.filterMap_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_inserted, ih]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
