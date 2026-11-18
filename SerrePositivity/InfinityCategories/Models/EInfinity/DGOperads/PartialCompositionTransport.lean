module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic

/-!
模型。文献の定義との比較は後で
# 部分合成と arity の等式による移送

概要：Berger–Moerdijk §1 の部分合成を、等しい arity の異なる自然数の式で比較する。
方針：arity の等式で添字を同一視し、係数と入力位置の移送を明示する。
規約：移送には等式の射と `Fin.cast` を用いる。
使われ方：反復合成と部分合成の arity の括弧付けを比較する。
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

/-- 概要：部分合成は外側と内側の arity の等式の移送と両立する（Berger–Moerdijk §1）。
方針：二つの arity の等式で入力を同一視する。
規約：代入位置も外側 arity の等式で移す。
使われ方：二入力への合成で現れる加法の括弧付けを整理する。 -/
lemma comp_index_eq (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (i : Fin (m + 1)) :
    (eqToHom (congrArg P.arity (congrArg (· + 1) hm)) ⊗ₘ eqToHom (congrArg P.arity hn)) ≫
      P.comp m' n' (Fin.cast (congrArg (· + 1) hm) i) =
        P.comp m n i ≫ eqToHom (congrArg P.arity (congrArg₂ (· + ·) hm hn)) := by
  subst m'
  subst n'
  simp only [eqToHom_refl, Fin.cast_refl, tensorHom_id, id_whiskerRight,
    Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
