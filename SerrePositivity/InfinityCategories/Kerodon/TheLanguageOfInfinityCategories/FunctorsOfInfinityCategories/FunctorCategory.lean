module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：通常の関手圏の nerve を nerve 間の関手単体集合と同型にする。
方針：nerve の充満忠実性と左随伴の有限積保存から指数比較の同型性を使う。
規約：対象と射の宇宙を同じ u に固定する。
使われ方：B5 の自然変換・随伴と pointwise Kan 拡張の古典比較。

対応節は Kerodon 1.5（Tag 0055）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

/-- 概要：nerve は指数対象を保つ。
方針：充満忠実な右随伴の左随伴が二項積を保つという一般定理を使う。
規約：Cat の対象と射の宇宙は u。
使われ方：関手圏の nerve の指数比較を同型にする。 -/
lemma nerveFunctor_monoidalClosed : MonoidalClosedFunctor nerveFunctor.{u, u} :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts nerveFunctor nerveAdjunction

attribute [local instance] nerveFunctor_monoidalClosed

/-- 概要：通常の関手圏の nerve は二つの nerve 間の関手単体集合と同型。
方針：nerve の指数比較の指定成分を取る。
規約：指定した通常の圏 C と D をそのまま使う。
使われ方：通常の自然変換を元の関手圏内の射として扱う。 -/
@[kerodon 0062, kerodon 0063]
def nerveFunctorCategoryIso (C D : Type u) [Category.{u} C] [Category.{u} D] :
    nerve (C ⥤ D) ≅ (ihom (nerve C)).obj (nerve D) :=
  asIso ((expComparison nerveFunctor (Cat.of C)).natTrans.app (Cat.of D))

/-- 概要：関手圏の nerve の比較同型は後合成に自然。
方針：指数比較の自然変換の自然性を読む。
規約：通常の後合成関手と nerve の射を指定する。
使われ方：古典自然変換の後合成と元の関手圏の作用の一致。 -/
lemma nerveFunctorCategoryIso_postcomp {C D E : Type u}
    [Category.{u} C] [Category.{u} D] [Category.{u} E] (F : D ⥤ E) :
    nerveMap ((whiskeringRight C D E).obj F) ≫ (nerveFunctorCategoryIso C E).hom =
      (nerveFunctorCategoryIso C D).hom ≫ (ihom (nerve C)).map (nerveMap F) :=
  ((expComparison nerveFunctor (Cat.of C)).natTrans.naturality F.toCatHom)

/-- 概要：関手圏の指数比較の評価は通常の関手評価の nerve と一致する。
方針：指数比較の uncurry 公式の積比較の逆を消去する。
規約：nerve の積比較を明示して始域を揃える。
使われ方：通常の関手頂点と自然変換の単体ごとの計算。 -/
@[kerodon 0062]
lemma nerveFunctorCategoryIso_uncurry (C D : Type u) [Category.{u} C] [Category.{u} D] :
    CartesianMonoidalCategory.prodComparison nerveFunctor (Cat.of C) (Cat.of (C ⥤ D)) ≫
      uncurry (nerveFunctorCategoryIso C D).hom =
        nerveFunctor.map ((ihom.ev (Cat.of C)).app (Cat.of D)) := by
  change CartesianMonoidalCategory.prodComparison nerveFunctor (Cat.of C)
      ((ihom (Cat.of C)).obj (Cat.of D)) ≫
    uncurry ((expComparison nerveFunctor (Cat.of C)).natTrans.app (Cat.of D)) = _
  rw [uncurry_expComparison, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories
