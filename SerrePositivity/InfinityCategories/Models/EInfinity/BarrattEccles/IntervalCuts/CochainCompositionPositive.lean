module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TripleGeneratorExt
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionVertexGenerators
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CompositionCoefficients
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OperadStructure

/-!
模型。文献の定義との比較は後で
# 正の内側 arity における区間余作用の部分合成則

概要：Berger–Fresse §2.2.6・§3.1 の部分合成則を全整数複体射の等式として閉じる。
方針：語基底と両頂点・辺での実際の等式を三重テンソルの外延性で延長する。
規約：任意の可換環、正の内側 arity、全整数次数と任意の係数。
使われ方：χ-coalgebra の部分合成公理の正 arity 部分。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：具体的な区間余作用は正の内側 arity の部分合成を保つ（BF §2.2.6・§3.1）。
方針：二つの語基底と区間の三生成元で比較し、全整数複体射へ線形延長する。
規約：正の内側 arity だけを仮定し、余代数構造は仮定しない。
使われ方：χ の部分合成公理の正 arity 部分と、その実際の射への適用。 -/
lemma cochainAction_comp_positive (m n : ℕ) (i : Fin (m + 1)) (hn : 0 < n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexPartialComposition A m n i ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A (m + n) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.iteratedCochainAction A m n i := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coefficient_interval_hom_ext A (m + 1) n
  · intro d e v w b
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_composition_basis_vertex_eq_iterated A v w i hn b
  · intro d e v w
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_composition_basis_edge_eq_iterated A v w i hn

/-- 概要：χ オペラッドの実際の部分合成と区間余作用の正 arity 公理（BF §3.1）。
方針：具体的な部分合成則をオペラッドの comp と二段作用の四射で表示する。
規約：正の内側 arity、任意の係数と整数次数。
使われ方：余代数構造の comp フィールドへ直接代入する等式。 -/
lemma cochainAction_operad_comp_positive (m n : ℕ) (i : Fin (m + 1)) (hn : 0 < n) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.operad A).comp m n i ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A (m + n) =
      ((β_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n)).hom ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫
        (α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A (m + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) m n i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_comp_positive A m n i hn

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
