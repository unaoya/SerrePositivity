module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance

/-!
模型。文献の定義との比較は後で
# 反復合成の最初の部分合成の arity の移送

概要：Berger–Moerdijk §1 の最後の入力への部分合成を、等しい arity の別の表記へ移す。
方針：外側 arity の和と指定した arity の等式で同一視する。
規約：代入位置 n と内側 arity l を保つ。
使われ方：反復合成の末尾二段を任意の二位置への合成と比較する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：再帰の最初の部分合成の外側 arity を等しい数へ移す（Berger–Moerdijk §1）。
方針：arity の等式で新しい変数を置き換え、元の定義に帰着する。
規約：始域と終域の移送を明示し、代入位置 n を保つ。
使われ方：二段の再帰に現れる加法の括弧付けを二位置への合成とそろえる。 -/
lemma composeFirstInputInsertion_at (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k l m : ℕ) (h : n + k = m) :
    P.composeFirstInputInsertion n k l =
      (eqToHom (congrArg P.arity (by omega : n + 1 + k = m + 1)) ▷ P.arity l) ≫
        P.comp m l ⟨n, by omega⟩ ≫
          eqToHom (congrArg P.arity (by omega : m + l = n + (k + l))) := by
  subst m
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
