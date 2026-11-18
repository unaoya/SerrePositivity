module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.NestedInsertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionNestedBase

/-!
模型。文献の定義との比較は後で
# 入れ子の反復合成の尾の移送

概要：Berger–Moerdijk §1 の入れ子の反復合成で更新される尾と総 arity を比較する。
方針：等しい尾の長さでは置き換えを使い、先頭合成の出力の移送をまとめる。
規約：入力族の順序と代入位置は固定する。
使われ方：反復合成の結合則の帰納仮定を更新後の尾へ適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：反復合成は等しい尾の長さの移送と両立する（Berger–Moerdijk §1）。
方針：尾の長さの等式で型を同一視する。
規約：指定入力の族 s は固定する。
使われ方：m+(k+l) と (m+k)+l の尾を持つ再帰呼び出しを比較する。 -/
@[reassoc]
lemma composeFirstInputs_tail_cast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) {k l : ℕ} (h : k = l)
    (s : Fin n → ℕ) :
    (eqToHom (congrArg P.arity (congrArg (n + ·) h)) ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫ P.composeFirstInputs n l s =
    P.composeFirstInputs n k s ≫
      eqToHom (congrArg P.arity (congrArg ((∑ i, s i) + ·) h)) := by
  subst l
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]

/-- 概要：先頭への合成は内側の総 arity を保つ分解の変更と両立する（Berger–Moerdijk §1）。
方針：内側の入力 arity の移送を吸収し、出力の二つの移送を一つにまとめる。
規約：指定入力数 n と尾 k の個別の値は変えてよい。
使われ方：最後の arity を代入した後の総和を再帰の出力へ合わせる。 -/
@[reassoc]
lemma composeIntoFirst_index_eq (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k n' k' : ℕ)
    (h : n + k = n' + k') :
    (P.arity (m + 1) ◁ eqToHom (congrArg P.arity h)) ≫ P.composeIntoFirst m n' k' =
      P.composeIntoFirst m n k ≫ eqToHom (congrArg P.arity
        (by omega : n + (m + k) = n' + (m + k'))) := by
  rw [P.composeIntoFirst_input_cast m n' k' h]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst
  rw [Category.assoc, eqToHom_trans]

/-- 概要：正規化した先頭合成に対する空の入力族の入れ子の結合則（Berger–Moerdijk §1）。
方針：既存の空の族の結合則に出力の arity の移送を後合成する。
規約：両辺の出力を (∑ s)+(m+k) にそろえる。
使われ方：composeIntoFirst を用いた反復合成の結合則の帰納法の基底となる。 -/
lemma composeIntoFirst_nested_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k : ℕ) (s : Fin 0 → ℕ) :
    (P.composeIntoFirst m 0 k ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 0 (fun i => P.arity (s i))) ≫
      P.composeFirstInputs 0 (m + k) s =
    (α_ (P.arity (m + 1)) (P.arity (0 + k)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 0 (fun i => P.arity (s i)))).hom ≫
      (P.arity (m + 1) ◁ P.composeFirstInputs 0 k s) ≫
        P.composeIntoFirst m (∑ i, s i) k := by
  have h := congrArg (· ≫ eqToHom (congrArg P.arity
    (by omega : m + ((∑ i, s i) + k) = (∑ i, s i) + (m + k))))
      (P.composeFirstInputs_nested_zero m k s)
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst, comp_whiskerRight, Category.assoc] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
