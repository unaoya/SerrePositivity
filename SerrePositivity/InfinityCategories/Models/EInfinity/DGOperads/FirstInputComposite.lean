module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.PartialCompositionTransport

/-!
模型。文献の定義との比較は後で
# 先頭入力への合成と反復合成の arity

概要：Berger–Moerdijk §1 の先頭入力への部分合成を、内側の指定入力と未代入の尾で表す。
方針：部分合成の出力を反復合成の n+(m+k) の表記へ移す。
規約：内側 n+k 入力の後に外側の残り m 入力が続き、位置の置換は加えない。
使われ方：入れ子の反復合成の結合則の始域と終域をそろえる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭入力への部分合成は内側 arity の移送と両立する（Berger–Moerdijk §1）。
方針：部分合成の添字の移送を、外側 arity を固定して適用する。
規約：代入位置は 0。
使われ方：入れ子の結合則の内側 arity の括弧付けを変更する。 -/
@[reassoc]
lemma comp_first_input_cast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m : ℕ) {r s : ℕ} (h : r = s) :
    (P.arity (m + 1) ◁ eqToHom (congrArg P.arity h)) ≫ P.comp m s 0 =
      P.comp m r 0 ≫ eqToHom (congrArg P.arity (congrArg (m + ·) h)) := by
  simpa only [eqToHom_refl, id_tensorHom, Fin.cast_refl, id_eq] using
    P.comp_index_eq (Eq.refl m) h (0 : Fin (m + 1))

/-- 概要：部分合成の外側 arity の移送は代入位置と出力の移送で表せる（Berger–Moerdijk §1）。
方針：内側 arity を固定した部分合成の添字の移送を使う。
規約：位置は Fin.cast で移す。
使われ方：反復合成の最初の代入を nested_assoc の arity へ合わせる。 -/
@[reassoc]
lemma comp_slot_output_cast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {r s : ℕ} (h : r = s) (l : ℕ)
    (j : Fin (r + 1)) :
    (eqToHom (congrArg P.arity (congrArg (· + 1) h)) ▷ P.arity l) ≫
      P.comp s l (Fin.cast (congrArg (· + 1) h) j) =
    P.comp r l j ≫ eqToHom (congrArg P.arity (congrArg (· + l) h)) := by
  simpa only [eqToHom_refl, tensorHom_id] using P.comp_index_eq h (Eq.refl l) j

/-- 概要：n+k 入力の演算を先頭入力へ合成し、出力を n+(m+k) で表す（Berger–Moerdijk §1）。
方針：先頭入力への部分合成に arity の等式の射を後合成する。
規約：入力の順序を変える全単射は使わない。
使われ方：内側の先頭 n 入力への代入と外側合成の交換を述べる。 -/
def composeIntoFirst (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k : ℕ) :
    P.arity (m + 1) ⊗ P.arity (n + k) ⟶ P.arity (n + (m + k)) :=
  P.comp m (n + k) 0 ≫ eqToHom (congrArg P.arity (by omega : m + (n + k) = n + (m + k)))

/-- 概要：先頭入力への正規化した合成は内側 arity の移送を吸収する（Berger–Moerdijk §1）。
方針：内側 arity の移送を部分合成の後へ運び、出力の二つの等式の射をまとめる。
規約：比較前の内側 arity r は n+k と等しければよい。
使われ方：入れ子の反復合成の結合則で更新した尾の arity を移送する。 -/
@[reassoc]
lemma composeIntoFirst_input_cast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n k : ℕ) {r : ℕ} (h : r = n + k) :
    (P.arity (m + 1) ◁ eqToHom (congrArg P.arity h)) ≫ P.composeIntoFirst m n k =
      P.comp m r 0 ≫ eqToHom (congrArg P.arity (by omega : m + r = n + (m + k))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeIntoFirst
  rw [P.comp_first_input_cast_assoc m h, eqToHom_trans]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
