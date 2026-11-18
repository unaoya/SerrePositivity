module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAfterInputs
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionNestedTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyBlockSum
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySubstitutionBlocks
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionEmptyTail

/-!
模型。文献の定義との比較は後で
# 入力を二ブロックに分けた反復合成

概要：Berger–Moerdijk §1 の全入力への合成を、後半の合成と前半の合成で記述する。
方針：有限テンソル族を分離し、後半を係数の直後へ移して代入する。
規約：出力を全入力の arity の和と未代入の尾の和に統一する。
使われ方：Schur 作用の部分合成則の係数側のブロック分解に用いる。
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

/-- 概要：後半を先に、前半を後に代入する二ブロックの反復合成射（Berger–Moerdijk §1）。
方針：二部分へのテンソル分離、後半の反復代入、前半の反復代入を合成する。
規約：最後に arity の和の分解の等式で全入力の和へ戻す。
使われ方：全入力への反復合成のブロック分解の右辺となる。 -/
def composeByBlocks (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n m k : ℕ) (s : Fin (n + m) → ℕ) :
    P.arity (n + m + k) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => P.arity (s j)) ⟶
      P.arity ((∑ j, s j) + k) :=
  (P.arity (n + m + k) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => P.arity (s j))).hom) ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (P.composeAfterInputs n m k (fun j => s (j.natAdd n)))
      (P.composeFirstInputs n ((∑ j : Fin m, s (j.natAdd n)) + k)
        (fun j => s (j.castAdd m))) ≫
    eqToHom (congrArg P.arity (by
      have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s
      omega : (∑ j : Fin n, s (j.castAdd m)) + ((∑ j : Fin m, s (j.natAdd n)) + k) =
        (∑ j, s j) + k))

/-- 概要：後半が空の二ブロック合成は通常の反復合成に一致する（Berger–Moerdijk §1）。
方針：空の後半の代入を単位子で相殺し、尾の長さの移送と出力の移送をまとめる。
規約：前半 n 入力へ代入し、尾 k 入力を保つ。
使われ方：二ブロック分解の後半の長さに関する帰納法の基底となる。 -/
lemma composeByBlocks_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin (n + 0) → ℕ) :
    P.composeByBlocks n 0 k s = P.composeFirstInputs n k s := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeByBlocks
  rw [P.composeAfterInputs_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt_zero]
  erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_empty_tail
    (eqToHom (congrArg P.arity (by simp : n + k =
      n + ((∑ j : Fin 0, s (j.natAdd n)) + k))))
    (P.composeFirstInputs n ((∑ j : Fin 0, s (j.natAdd n)) + k)
      (fun j => s (j.castAdd 0))))]
  rw [P.composeFirstInputs_tail_cast_assoc n
    (by simp : k = (∑ j : Fin 0, s (j.natAdd n)) + k) (fun j => s (j.castAdd 0)),
    eqToHom_trans]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
