module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ChainMap
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Complex

/-!
模型。文献の定義との比較は後で
# 非有界整数コチェイン上の全射 TR

概要：Berger–Fresse §1.3 の一般の TR を本来の整数コチェイン複体の射へ移す。
方針：既存の鎖写像を次数 q ↦ −q の延長関手で送る。
規約：全ての負次数成分は元の正規化 TR、正次数は零対象間の射。
使われ方：TR を対称 dg オペラッドの射として束ねる基礎の複体射。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：実際の E(n) から χ(n) への整数コチェイン TR（BF §1.3）。
方針：全 arity の微分保存を持つ鎖写像を零延長する。
規約：非有界整数コチェイン複体の射として定義する。
使われ方：TR オペラッド射の各 arity 成分。 -/
def cochainMap (n : ℕ) : _root_.SerrePositivity.EInfinity.BarrattEccles.complex A n ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.chainMap A n)

/-- 概要：整数 TR の次数 −d 成分は既存の正規化 TR（BF §1.3）。
方針：延長した射の標準成分公式を使う。
規約：左右の比較同型は BE と χ の零延長によるもの。
使われ方：合成・単位・同変性の成分法則を整数 TR へ移す。 -/
lemma cochainMap_f (n d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n).f (-(d : ℤ)) = (_root_.SerrePositivity.EInfinity.BarrattEccles.complexXIso A n d).hom ≫
      ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).inv :=
  HomologicalComplex.extendMap_f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.chainMap A n) ComplexShape.embeddingDownNat rfl

/-- 概要：整数 TR の全非正次数成分は全射（BF §1.3.4）。
方針：正規化 TR の全射性を両側の比較同型で移す。
規約：任意の可換環と零を含む全 arity。
使われ方：整数複体のオペラッド法則の移送と射の全射性。 -/
lemma cochainMap_f_surjective (n d : ℕ) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n).f (-(d : ℤ))).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_f]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).toLinearEquiv.symm.surjective.comp
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n d).comp
      (_root_.SerrePositivity.EInfinity.BarrattEccles.complexXIso A n d).toLinearEquiv.surjective)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
