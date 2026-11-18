module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ArityBijectionFunctor

/-!
模型。文献の定義との比較は後で
# 二入力の代入後の前方への反復合成

概要：Berger–Moerdijk §1 の末尾二入力を代入した後に残る前方への合成を記述する。
方針：二入力の代入後の arity を前方と尾へ分離し、既存の反復合成を適用する。
規約：尾の長さの表記は (k+a)+b とし、前方の入力族は変えない。
使われ方：末尾二入力の交換で誘導されるブロック交換を合成の出力へ移す。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arityBijectionMap _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs

/-- 概要：末尾二入力を代入した後に前方 n 入力へ残りの演算を合成する（Berger–Moerdijk §1）。
方針：arity の括弧を前方と尾に分け、前方への既存の反復合成を適用する。
規約：二入力の arity a,b と未代入入力 k 個を尾に残す。
使われ方：二位置への合成の後の係数射として用いる。 -/
def composeFirstInputsAfterTwo (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k a b : ℕ) (s : Fin n → ℕ) :
    P.arity (((n + k) + a) + b) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i)) ⟶
      P.arity ((∑ i, s i) + ((k + a) + b)) :=
  (eqToHom (congrArg P.arity
      (by omega : ((n + k) + a) + b = n + ((k + a) + b))) ▷
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫
      P.composeFirstInputs n ((k + a) + b) s

/-- 概要：二入力の代入後のブロック交換は残りの反復合成の出力の尾の交換へ移る（Berger–Moerdijk §1）。
方針：前方の分離と交換の両立を使い、尾の全単射に関する反復合成の等変性を適用する。
規約：前方の入力族は固定し、a,b の二ブロックを交換する。
使われ方：末尾二入力の合成の外側等変性の残りの係数射の可換性を与える。 -/
lemma composeFirstInputsAfterTwo_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k a b : ℕ)
    (s : Fin n → ℕ) :
    (P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap n k a b) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫
        P.composeFirstInputsAfterTwo n k b a s =
      P.composeFirstInputsAfterTwo n k a b s ≫
        P.arityBijectionMap (_root_.SerrePositivity.FiniteBijection.blockEquiv
          (Equiv.refl (Fin (∑ i, s i))) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap k a b)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputsAfterTwo]
  rw [← Category.assoc, ← comp_whiskerRight,
    P.arityBijectionMap_context_tail_pre n k a b, comp_whiskerRight, Category.assoc]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arityBijectionMap
  rw [P.composeFirstInputs_tail_bijection n ((k + a) + b) ((k + b) + a) s
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadTailBlockSwap k a b)]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
