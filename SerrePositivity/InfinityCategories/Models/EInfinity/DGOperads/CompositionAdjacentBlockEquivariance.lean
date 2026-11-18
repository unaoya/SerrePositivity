module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacentValues

/-!
模型。文献の定義との比較は後で
# 反復合成の隣接交換と入力ブロックの交換

概要：Berger–Moerdijk §1 の全入力への合成の外側等変性をブロック交換で表す。
方針：末尾から再帰した出力と先頭から再帰した出力の値が一致することを使う。
規約：各入力ブロックの内部順序を保ち、未代入の尾は零個とする。
使われ方：Schur 対象の作用で係数側とテンソル冪側の隣接交換を一致させる。
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

/-- 概要：全入力への反復合成の隣接交換の出力はテンソル族のブロック交換と一致する（Berger–Moerdijk §1）。
方針：両方の全単射の値を前方、左ブロック、右ブロック、後方の四区間で比較する。
規約：始域と終域の零との和は定義的に同一視する。
使われ方：合成の等変性とテンソル冪の連結の等変性に同じ出力の全単射を使う。 -/
lemma operadCompositionAdjacentOutput_zero_eq (n : ℕ) (s : Fin (n + 1) → ℕ)
    (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput n 0 s i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentBlockEquiv n s i := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput_val n 0 s i x).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentBlockEquiv_val n s i x).symm

namespace Operad

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：全入力への合成は隣接する入力の交換を標準のブロック交換へ写す（Berger–Moerdijk §1）。
方針：既存の合成の隣接交換の等変性に出力の全単射の同定を適用する。
規約：出力にはテンソル冪の連結で用いる tensorFamilyAdjacentBlockEquiv が作用する。
使われ方：Schur 対象の作用の外側等変性の隣接交換の場合となる。 -/
lemma composition_adjacent_block_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ)
    (s : Fin (n + 1) → ℕ) (i : Fin n) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1) (adjacentTransposition i)) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => P.arity (s j)) i).hom) ≫
        P.composition (n + 1) (fun j => s (adjacentTransposition i j)) =
      P.composition (n + 1) s ≫
        P.arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentBlockEquiv n s i) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput_zero_eq] using
    P.composition_adjacent_equivariance n s i

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
