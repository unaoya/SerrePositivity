module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiniteSubcomplexFactorization

/-!
概要：具体的な連続 Kan 関手への有限射は有限部分複体の像を経由する。
方針：実際に証明した filtered 余極限保存を有限部分複体表示へ適用する。
規約：この関手の連続性や値の Kan 性に追加入力は不要。単位の弱同値性は別の工程。
使われ方：filtered ∞ 圏の弱可縮性で必要な有限境界の因子分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：連続 Kan 関手の値への有限射はある有限部分複体の値を経由する。
方針：具体的な関手の保存性を一般の有限部分複体因子分解へ渡す。
規約：元の指定射との合成の等式を返す。
使われ方：有限境界や有限パラメータの元の有限な台への下降。 -/
lemma continuousKanReplacement_finite_factorization {K X : SSet.{u}} [K.Finite]
    (f : K ⟶ continuousKanReplacement.obj X) :
    ∃ A : FiniteSubcomplex X, ∃ g : K ⟶ continuousKanReplacement.obj A.val,
      g ≫ continuousKanReplacement.map A.val.ι = f :=
  finiteSubcomplex_factorization_after_preserving_functor continuousKanReplacement X f

/-- 概要：連続 Kan 関手の値への境界は元の有限部分複体の値を経由する。
方針：有限形状の因子分解を標準境界に適用する。
規約：零次元の空境界も含む。使われ方：一般の filtered ∞ 圏の弱可縮性の有限検査。 -/
lemma continuousKanReplacement_boundary_factorization (X : SSet.{u}) (n : ℕ)
    (f : (boundary n : SSet.{u}) ⟶ continuousKanReplacement.obj X) :
    ∃ A : FiniteSubcomplex X,
      ∃ g : (boundary n : SSet.{u}) ⟶ continuousKanReplacement.obj A.val,
        g ≫ continuousKanReplacement.map A.val.ι = f :=
  continuousKanReplacement_finite_factorization f

end SerrePositivity.InfinityCategories.F2
