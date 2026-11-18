module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NullaryEdgeComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NullaryVertexComposition

/-!
模型。文献の定義との比較は後で
# 全 arity の区間余作用の部分合成則

概要：Berger–Fresse §2.2.6・§3.1 の部分合成則を全整数複体射として証明する。
方針：両頂点・辺での全 arity の比較を語基底と三入力外延性で延長する。
規約：任意の可換環、nullary、出力 arity 零と全整数次数。
使われ方：具体的な区間の χ-coalgebra 構造の部分合成公理。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：具体的な区間余作用は全ての部分合成を保つ（BF §2.2.6・§3.1）。
方針：両頂点と辺の等式を三入力外延性で延長し、空語の正次数は空性で除く。
規約：nullary と出力 arity 零を含み、モデル構造・余代数構造は仮定しない。
使われ方：全 arity の χ-coalgebra の部分合成公理。 -/
lemma cochainAction_comp (m n : ℕ) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A (m + n) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.iteratedCochainAction A m n i := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coefficient_interval_hom_ext A (m + 1) n
  · intro d e v w b
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_composition_basis_vertex_eq_iterated_all A v w i b
  · intro d e v w
    cases n with
    | zero =>
      cases e with
      | zero => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_composition_basis_edge_nullary_eq_iterated A v w i
      | succ e => exact isEmptyElim w
    | succ n => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_composition_basis_edge_eq_iterated A v w i (by omega)

/-- 概要：χ の実際の部分合成と区間余作用の全 arity 公理（BF §3.1）。
方針：具体的な合成則をオペラッドの comp と二段作用の四射で表示する。
規約：nullary・全整数次数・任意の係数を含む。
使われ方：Operad.Coalgebra の comp_coaction フィールドへ直接渡す。 -/
lemma cochainAction_operad_comp (m n : ℕ) (i : Fin (m + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.operad A).comp m n i ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A (m + n) =
      ((β_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n)).hom ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫
        (α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A (m + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) m n i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_comp A m n i

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
