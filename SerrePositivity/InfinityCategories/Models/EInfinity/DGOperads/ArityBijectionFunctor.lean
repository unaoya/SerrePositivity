module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionTailBijection
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TailBlockSwap

/-!
模型。文献の定義との比較は後で
# arity の有限全単射と長さの移送

概要：Berger–Moerdijk §1 の反復合成で用いる有限全単射と arity の等式の射を比較する。
方針：対称列の関手の恒等射則・合成則を使い、長さの等式では置き換えを行う。
規約：全単射の合成は左を先に適用する Equiv.trans の向き。
使われ方：二入力への合成後のブロック交換を未代入の尾の全単射へ移す。
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

/-- 概要：標準有限集合の全単射をオペラッドの arity 間の射として評価する（Berger–Moerdijk §1）。
方針：対称列の関手を有限全単射の亜群の射で評価する。
規約：始域と終域の長さの式は異なってよい。
使われ方：ブロック交換と arity の等式による移送の計算に用いる。 -/
def arityBijectionMap (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {m n : ℕ} (e : Fin m ≃ Fin n) :
    P.arity m ⟶ P.arity n :=
  P.sequence.map (_root_.SerrePositivity.FiniteBijection.homOfEquiv
    (X := _root_.SerrePositivity.FiniteBijection.of m) (Y := _root_.SerrePositivity.FiniteBijection.of n) e)

/-- 概要：arity の恒等全単射の作用は恒等射である（Berger–Moerdijk §1）。
方針：有限全単射の恒等射と関手の恒等射則を使う。
規約：arity は任意の自然数。
使われ方：長さの等式による移送の計算の基底に用いる。 -/
lemma arityBijectionMap_refl (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) :
    P.arityBijectionMap (Equiv.refl (Fin n)) = 𝟙 (P.arity n) := by
  exact (congrArg (fun f : _root_.SerrePositivity.FiniteBijection.of n ⟶ _root_.SerrePositivity.FiniteBijection.of n =>
    P.sequence.map f) (_root_.SerrePositivity.FiniteBijection.homOfEquiv_refl (_root_.SerrePositivity.FiniteBijection.of n))).trans
      (P.sequence.map_id (_root_.SerrePositivity.FiniteBijection.of n))

/-- 概要：arity の全単射の合成は射の合成に移る（Berger–Moerdijk §1）。
方針：有限全単射の合成と関手の合成則を使う。
規約：e を先に適用し、その後 f を適用する。
使われ方：ブロック交換を前方と尾の全単射へ分解する。 -/
lemma arityBijectionMap_trans (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {l m n : ℕ}
    (e : Fin l ≃ Fin m) (f : Fin m ≃ Fin n) :
    P.arityBijectionMap (e.trans f) = P.arityBijectionMap e ≫ P.arityBijectionMap f := by
  exact (congrArg (fun g : _root_.SerrePositivity.FiniteBijection.of l ⟶ _root_.SerrePositivity.FiniteBijection.of n =>
    P.sequence.map g) (_root_.SerrePositivity.FiniteBijection.homOfEquiv_trans
      (X := _root_.SerrePositivity.FiniteBijection.of l) (Y := _root_.SerrePositivity.FiniteBijection.of m)
      (Z := _root_.SerrePositivity.FiniteBijection.of n) e f)).trans
        (P.sequence.map_comp
          (_root_.SerrePositivity.FiniteBijection.homOfEquiv (X := _root_.SerrePositivity.FiniteBijection.of l) (Y := _root_.SerrePositivity.FiniteBijection.of m) e)
          (_root_.SerrePositivity.FiniteBijection.homOfEquiv (X := _root_.SerrePositivity.FiniteBijection.of m) (Y := _root_.SerrePositivity.FiniteBijection.of n) f))

/-- 概要：長さの等式の標準全単射は arity の等式の射に移る（Berger–Moerdijk §1）。
方針：長さの等式で置き換え、恒等全単射の場合を使う。
規約：長さの等式の証明には依存しない。
使われ方：ブロック交換の前後の括弧の移送を等式の射に直す。 -/
lemma arityBijectionMap_finCongr (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {m n : ℕ} (h : m = n) :
    P.arityBijectionMap (finCongr h) = eqToHom (congrArg P.arity h) := by
  subst n
  exact P.arityBijectionMap_refl m

/-- 概要：前後を固定するブロック交換の作用は前方と尾への分離で計算できる（Berger–Moerdijk §1）。
方針：全単射の尾への分解に関手の合成則を適用し、長さの移送を等式の射へ直す。
規約：前方 p 個を固定し、尾の a,b の二ブロックを交換する。
使われ方：二入力への合成の出力の交換を残りの反復合成へ移す。 -/
lemma arityBijectionMap_context_tail (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (p q a b : ℕ) :
    P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b) =
      eqToHom (congrArg P.arity
        (by omega : ((p + q) + a) + b = p + ((q + a) + b))) ≫
        P.arityBijectionMap
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin p)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap q a b)) ≫
        eqToHom (congrArg P.arity
          (by omega : p + ((q + b) + a) = ((p + q) + b) + a)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_tail, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arityBijectionMap_trans,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arityBijectionMap_finCongr]

/-- 概要：ブロック交換の後に前方を分離すると、先に前方を分離して尾を交換する射に一致する（Berger–Moerdijk §1）。
方針：全単射の尾への分解の末尾の移送を、逆の移送と相殺する。
規約：始域は前後を固定した二ブロック交換の元の arity。
使われ方：二入力の代入後の残りの反復合成の前へ尾の全単射を置く。 -/
lemma arityBijectionMap_context_tail_pre (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (p q a b : ℕ) :
    P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap p q a b) ≫
        eqToHom (congrArg P.arity
          (by omega : ((p + q) + b) + a = p + ((q + b) + a))) =
      eqToHom (congrArg P.arity
        (by omega : ((p + q) + a) + b = p + ((q + a) + b))) ≫
        P.arityBijectionMap
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin p)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap q a b)) := by
  rw [P.arityBijectionMap_context_tail p q a b]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- 概要：反復合成は未代入の尾の長さの等式による移送と両立する（Berger–Moerdijk §1）。
方針：尾の長さを等式で置き換え、恒等の移送を簡約する。
規約：前方の入力族は固定する。
使われ方：末尾二入力の代入後の尾の長さの括弧と順序の表記をそろえる。 -/
lemma composeFirstInputs_tail_index_eq (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) {k l : ℕ}
    (h : k = l) (s : Fin n → ℕ) :
    (eqToHom (congrArg P.arity (congrArg (n + ·) h)) ▷
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫ P.composeFirstInputs n l s =
      P.composeFirstInputs n k s ≫
        eqToHom (congrArg P.arity (congrArg ((∑ i, s i) + ·) h)) := by
  subst l
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
