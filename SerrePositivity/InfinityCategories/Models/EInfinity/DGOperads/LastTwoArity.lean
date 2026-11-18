module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TwoSlotSubstitutionTransport

/-!
模型。文献の定義との比較は後で
# 末尾二入力の交換の始域と終域の arity

概要：Berger–Moerdijk §1 の末尾交換の外側等変性で用いる arity 間の全単射を記述する。
方針：外側の交換を arity の括弧の移送に通し、出力では前方を固定した尾の交換を用いる。
規約：元の外側の arity は n+2+k、分離後は (n+k)+2。
使われ方：分離後の末尾交換の等変性を元の反復合成へ接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

/-- 概要：前方 n+2 入力の最後の二位置を交換し未代入入力 k 個を保つ（Berger–Moerdijk §1）。
方針：全入力の標準有限集合の n 番目と n+1 番目の互換を取る。
規約：入力位置は 0 始まり。
使われ方：元の外側の arity に作用する末尾交換を指定する。 -/
def operadLastTwoInputSwap (n k : ℕ) : Equiv.Perm (Fin (n + 2 + k)) :=
  Equiv.swap ⟨n, by omega⟩ ⟨n + 1, by omega⟩

/-- 概要：外側の末尾交換は arity の括弧の移送後にも同じ二位置の交換となる（Berger–Moerdijk §1）。
方針：全単射による互換の共役の式を使い、二位置の値を比較する。
規約：移送後の arity は (n+k)+2。
使われ方：外側の交換作用を分離後の係数の arity へ移す。 -/
lemma operadLastTwoInputSwap_transport (n k : ℕ) :
    (finCongr (by omega : n + 2 + k = (n + k) + 2)).permCongr
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoInputSwap n k) =
      Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩ := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoInputSwap, Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
  congr 1

/-- 概要：末尾交換の出力の全単射を全入力の和の arity 間に定義する（Berger–Moerdijk §1）。
方針：前半と尾へ長さを移し、尾の二ブロックを交換して交換後の全入力の和へ戻す。
規約：前半の各ブロックと元の未代入入力の内部の順序を保つ。
使われ方：反復合成の外側等変性の出力に作用する。 -/
def operadLastTwoOutputEquiv (n k : ℕ) (s : Fin (n + 2) → ℕ) :
    Fin ((∑ i, s i) + k) ≃
      Fin ((∑ i, s (adjacentTransposition (Fin.last n) i)) + k) :=
  (finCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoComposeOutput_eq n k s).symm).trans
    ((_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin (∑ i : Fin n, s i.castSucc.castSucc)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap k (s (Fin.last n).castSucc) (s (Fin.last (n + 1))))).trans
        (finCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoSwapOutput_eq n k s)))

namespace Operad

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：外側の末尾交換の作用は arity の括弧の移送と両立する（Berger–Moerdijk §1）。
方針：一般の置換作用の arity の移送と、互換の共役の計算を組み合わせる。
規約：交換する二位置の値は移送の前後で変わらない。
使われ方：元の反復合成の前の係数作用を分離後の係数作用に直す。 -/
lemma arity_lastTwoInputSwap_index (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) :
    P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoInputSwap n k)) ≫
        eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) =
      eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ≫
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + k) + 2)
          (Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩)) := by
  have h := (P.arity_permutation_index_eq
    (by omega : n + 2 + k = (n + k) + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoInputSwap n k)).symm
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoInputSwap_transport] at h
  exact h

/-- 概要：外側の末尾交換と内側の射をテンソルした作用は arity の移送と両立する（Berger–Moerdijk §1）。
方針：テンソル積の合成則で係数射をまとめ、外側の交換の移送の等式を使う。
規約：内側の複体射は任意でよい。
使われ方：末尾交換後の反復合成の始域の移送を交換作用の前へ移す。 -/
@[reassoc]
lemma arity_lastTwoInputSwap_tensor_index (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    {V W : Complex A} (b : V ⟶ W) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoInputSwap n k)) ⊗ₘ b) ≫
        (eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ▷ W) =
      (eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ▷ V) ≫
        (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((n + k) + 2)
          (Equiv.swap (⟨n, by omega⟩ : Fin ((n + k) + 2)) ⟨n + 1, by omega⟩)) ⊗ₘ b) := by
  simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [P.arity_lastTwoInputSwap_index n k]

/-- 概要：末尾交換の出力への作用は前半と尾への移送を介して計算できる（Berger–Moerdijk §1）。
方針：全単射の合成を射の合成へ写し、長さの標準全単射を等式の射へ直す。
規約：尾の二ブロックの交換以外の置換を入れない。
使われ方：反復合成後の出力の移送を相殺して尾の交換の等変性を用いる。 -/
lemma arity_lastTwoOutputEquiv (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin (n + 2) → ℕ) :
    P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoOutputEquiv n k s) =
      eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoComposeOutput_eq n k s).symm) ≫
        P.arityBijectionMap (_root_.SerrePositivity.FiniteBijection.blockEquiv
          (Equiv.refl (Fin (∑ i : Fin n, s i.castSucc.castSucc)))
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap k (s (Fin.last n).castSucc) (s (Fin.last (n + 1))))) ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoSwapOutput_eq n k s)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoOutputEquiv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arityBijectionMap_trans, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arityBijectionMap_finCongr]

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
