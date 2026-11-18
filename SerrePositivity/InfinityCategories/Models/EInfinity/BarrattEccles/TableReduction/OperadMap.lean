module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Morphism
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OperadStructure
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SequenceMap
public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure

/-!
模型。文献の定義との比較は後で
# 一般の table reduction オペラッド射

概要：Berger–Fresse §1.3 の TR : E → χ を全 arity の対称 dg オペラッド射として構成する。
方針：整数複体の自然変換と、構成済みの単位・全部分合成の保存をまとめる。
規約：任意の可換環と arity 零を含む非有界整数コチェイン複体。
使われ方：χ の区間切断作用を E の作用へ制限し、具体的な E-coalgebra 区間を作る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：実際の Barratt–Eccles から全射語オペラッドへの一般の TR（BF §1.3）。
方針：対称列の TR に単位と全ての部分合成の複体射の保存を付ける。
規約：零 arity を除外せず、保存則を仮定しない。
使われ方：χ-coalgebra を E-coalgebra に制限する係数の射。 -/
def operadMap : _root_.SerrePositivity.EInfinity.BarrattEccles.operad A ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.operad A where
  map := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sequenceMap A
  unit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexUnit_comm A
  comp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.complexPartialComposition_comm A

/-- 概要：TR オペラッド射の各成分は実際の整数 TR（BF §1.3）。
方針：オペラッド射と対称列の射を評価する。
規約：全 arity。
使われ方：複体上の計算をオペラッド射へ接続する。 -/
lemma operadMap_app (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.operadMap A).map.app (_root_.SerrePositivity.FiniteBijection.of n) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n := rfl

/-- 概要：TR オペラッド射の全整数成分は全射（BF §1.3.4）。
方針：構成した整数 TR の全射性をそのまま使う。
規約：任意の可換環、全 arity・全鎖次数。
使われ方：TR による作用の比較と具体的な生成元の持ち上げ。 -/
lemma operadMap_f_surjective (n : ℕ) (r : ℤ) :
    Function.Surjective (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.operadMap A).map.app (_root_.SerrePositivity.FiniteBijection.of n)).f r).hom :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_f_surjective_int A n r

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
