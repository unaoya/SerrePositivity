module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.PartialCompositionTransport

/-!
模型。文献の定義との比較は後で
# 後方の入力を残す先頭入力への部分合成

概要：Berger–Moerdijk §1 の異なる入力への代入を比較するため、先頭入力への合成を正規化する。
方針：前方一入力、続く m 入力、尾 k 入力の arity の表記を部分合成へ移す。
規約：先頭入力へ p 入力の演算を代入し、出力を p+m+k で表す。
使われ方：先頭への合成と後方の演算族への反復代入を交換する。
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

/-- 概要：先頭入力へ演算を代入し、その後の m 入力と尾 k 入力を残す（Berger–Moerdijk §1）。
方針：外側 arity を m+k+1 に移して先頭へ部分合成し、出力を p+m+k に移す。
規約：残す入力の順序と代入する演算の内部順序を変えない。
使われ方：先頭入力の部分合成と後半の反復合成の交換則を述べる。 -/
def composeAheadOfInputs (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k p : ℕ) :
    P.arity (1 + m + k) ⊗ P.arity p ⟶ P.arity (p + m + k) :=
  (eqToHom (congrArg P.arity (by omega : 1 + m + k = (m + k) + 1)) ▷ P.arity p) ≫
    P.comp (m + k) p 0 ≫
      eqToHom (congrArg P.arity (by omega : (m + k) + p = p + m + k))

/-- 概要：正規化した先頭への合成を、等しい外側 arity の別の表記で計算する（Berger–Moerdijk §1）。
方針：外側 arity の等式で変数を同一視する。
規約：代入位置は 0、内部 arity は p を保つ。
使われ方：二位置への合成の交換則の標準 arity へ移す。 -/
lemma composeAheadOfInputs_at (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k p r : ℕ) (h : m + k = r) :
    P.composeAheadOfInputs m k p =
      (eqToHom (congrArg P.arity (by omega : 1 + m + k = r + 1)) ▷ P.arity p) ≫
        P.comp r p 0 ≫ eqToHom (congrArg P.arity (by omega : r + p = p + m + k)) := by
  subst r
  rfl

/-- 概要：先頭への合成は残す入力の総数を保つ分解の変更と両立する（Berger–Moerdijk §1）。
方針：外側 arity を共通の m+k で表し、入力と出力の移送をまとめる。
規約：先頭へ代入する演算の arity p は固定する。
使われ方：後半の演算を一つずつ合成する帰納法で、更新した尾の括弧付けを移す。 -/
@[reassoc]
lemma composeAheadOfInputs_index_eq (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k m' k' p : ℕ)
    (he : m + k = m' + k') :
    (eqToHom (congrArg P.arity (by omega : 1 + m + k = 1 + m' + k')) ▷ P.arity p) ≫
      P.composeAheadOfInputs m' k' p =
    P.composeAheadOfInputs m k p ≫
      eqToHom (congrArg P.arity (by omega : p + m + k = p + m' + k')) := by
  rw [P.composeAheadOfInputs_at m' k' p (m + k) he.symm]
  rw [← comp_whiskerRight_assoc, eqToHom_trans]
  conv_rhs =>
    arg 1
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeAheadOfInputs
  simp only [Category.assoc, eqToHom_trans]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
