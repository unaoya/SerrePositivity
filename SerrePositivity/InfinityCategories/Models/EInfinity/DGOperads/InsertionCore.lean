module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Insertion

/-!
模型。文献の定義との比較は後で
# 前方と後方の入力数を明示したテンソル代入

概要：Berger–Moerdijk §1 の標準の入力代入射を、三つの入力区間の長さで表す。
方針：入力数と出力数の移送を構造射の外へ分け、区間長の等式の消去を使う。
規約：前方 s、内側 n、後方 t の順序を保つ。
使われ方：指定位置 a の代入で後半の長さ (a+b)-a を b へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：三つの入力区間の長さを明示した標準の代入射（Berger–Moerdijk §1）。
方針：前方の入力を越えて係数を移し、内側へ演算を適用して前方と後方を連結する。
規約：始域の入力数は s+(n+t)、終域は s+(t+1)。
使われ方：区間長の移送を代入の構造射から分離する。 -/
def tensorInsertionCore (X C : Complex A) (s n t : ℕ) (θ : C ⊗ power X n ⟶ X) :
    C ⊗ power X (s + (n + t)) ⟶ power X (s + (t + 1)) :=
  (C ◁ (appendIso X s (n + t)).inv) ≫
    (α_ C (power X s) (power X (n + t))).inv ≫
    ((β_ C (power X s)).hom ▷ power X (n + t)) ≫
    (α_ (power X s) C (power X (n + t))).hom ≫
    (power X s ◁ (C ◁ (appendIso X n t).inv)) ≫
    (power X s ◁ (α_ C (power X n) (power X t)).inv) ≫
    (power X s ◁ (θ ▷ power X t)) ≫ (appendIso X s (t + 1)).hom

/-- 概要：標準の代入射は区間長を明示した射へ入出力の移送を合成したものである（Berger–Moerdijk §1）。
方針：定義の最初の左 whisker を二つへ分け、合成の括弧を整理する。
規約：前方の長さは i.val、後方は m-i.val。
使われ方：代入位置と後半の長さを別の表示へ移す。 -/
lemma tensorInsertionAction_eq_core (X C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ power X n ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C m n i θ =
      (C ◁ eqToHom (congrArg (power X) (by omega : m + n = i.val + (n + (m - i.val))))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore X C i.val n (m - i.val) θ ≫
      eqToHom (congrArg (power X) (by omega : i.val + (m - i.val + 1) = m + 1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore, whiskerLeft_comp, Category.assoc]

/-- 概要：後半の長さの等しい表示を入出力の移送の中で同一視できる（Berger–Moerdijk §1）。
方針：長さの等式を消去し、移送の証明の一意性を使う。
規約：入出力の総数 R,T を固定して後半 t の表示だけを変える。
使われ方：後半の長さの減算を実際の後半の長さへ戻す。 -/
lemma tensorInsertionCore_transport (X C : Complex A) (s n : ℕ) {t t' : ℕ} (h : t = t')
    (θ : C ⊗ power X n ⟶ X) {R T : ℕ}
    (hin : R = s + (n + t)) (hin' : R = s + (n + t'))
    (hout : s + (t + 1) = T) (hout' : s + (t' + 1) = T) :
    (C ◁ eqToHom (congrArg (power X) hin)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore X C s n t θ ≫
      eqToHom (congrArg (power X) hout) =
    (C ◁ eqToHom (congrArg (power X) hin')) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore X C s n t' θ ≫
      eqToHom (congrArg (power X) hout') := by
  subst t'
  rfl

/-- 概要：位置 a への代入は前方 a、後方 b の区間長で計算できる（Berger–Moerdijk §1）。
方針：標準の代入を区間長の式へ移し、(a+b)-a=b の等式を消去する。
規約：外側の入力数は a+b+1。
使われ方：三ブロックの連結上で任意位置の代入を比較する。 -/
lemma tensorInsertionAction_at_sum (X C : Complex A) (a b n : ℕ)
    (θ : C ⊗ power X n ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C (a + b) n ⟨a, by omega⟩ θ =
      (C ◁ eqToHom (congrArg (power X) (by omega : a + b + n = a + (n + b)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore X C a n b θ ≫
      eqToHom (congrArg (power X) (by omega : a + (b + 1) = a + b + 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_eq_core]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore_transport X C a n (Nat.add_sub_cancel_left a b) θ
    (by omega) (by omega) (by omega) (by omega)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
