module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionLastSwapFactor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.LastTwoArity

/-!
模型。文献の定義との比較は後で
# 反復合成の末尾二入力の外側等変性

概要：Berger–Moerdijk §1 の前方への反復合成が、前方の末尾二入力の交換と両立することを示す。
方針：交換前後の因子分解に分離後の等変性を適用し、始域と終域の arity の移送を整理する。
規約：未代入の尾 k 個は保ち、出力では対応する二ブロックを交換する。
使われ方：任意の隣接交換の外側等変性の末尾の場合を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputsAfterTwo _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.twoSlotComposition

/-- 概要：前方への反復合成は末尾二入力の外側交換を出力の二ブロック交換に移す（Berger–Moerdijk §1）。
方針：交換後の因子分解と始域の移送の自然性を使い、分離後の等変性を適用して出力の移送を相殺する。
規約：前方 n+2 入力の最後の二位置を交換し、未代入入力 k 個の内部の順序を保つ。
使われ方：全入力への合成の任意の隣接交換に関する外側等変性の帰納法の基底に用いる。 -/
lemma composeFirstInputs_lastSwap_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ)
    (s : Fin (n + 2) → ℕ) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 2 + k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoInputSwap n k)) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) (fun i => P.arity (s i)) (Fin.last n)).hom) ≫
        P.composeFirstInputs (n + 2) k (fun i => s (adjacentTransposition (Fin.last n) i)) =
      P.composeFirstInputs (n + 2) k s ≫
        P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoOutputEquiv n k s) := by
  have h := congrArg (fun f =>
      (eqToHom (congrArg P.arity (by omega : n + 2 + k = (n + k) + 2)) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => P.arity (s i))) ≫ f ≫
        eqToHom (congrArg P.arity (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoSwapOutput_eq n k s)))
    (P.composeFirstInputs_lastSwap_separated n k s)
  simp only [Category.assoc] at h
  conv_lhs =>
    arg 2
    rw [P.composeFirstInputs_lastSwap_factor n k s]
  rw [P.arity_lastTwoInputSwap_tensor_index_assoc n k
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) (fun i => P.arity (s i)) (Fin.last n)).hom]
  conv_rhs =>
    arg 1
    rw [P.composeFirstInputs_twoSlot_after_factor n k s]
  conv_rhs =>
    arg 2
    rw [P.arity_lastTwoOutputEquiv n k s]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
