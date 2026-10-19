module

public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTrans
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：通常の圏の指定同値を元の nerve 間の同値へ写す。
方針：単位と余単位の自然同型を h Fun の指定同型へ写す。
規約：同じ宇宙の小さい圏と単体集合を扱う。
使われ方：B5 の通常の錐と native な錐の族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {D E : Type u} [Category.{u} D] [Category.{u} E]

/-- 概要：通常の圏の指定同値は元の nerve 間の QCat の同値を与える。
方針：単位と余単位の自然同型を h Fun の指定同型へ写す。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
def kanNerveQCatEquivalence (e : D ≌ E) : QCatEquivalence (nerve D) (nerve E) where
  hom := nerveMap e.functor
  inv := nerveMap e.inverse
  homInvIso := by
    change (kanNerveFunctorHomEmbedding D D).obj (e.functor ⋙ e.inverse) ≅
      (kanNerveFunctorHomEmbedding D D).obj (𝟭 D)
    exact (kanNerveFunctorHomEmbedding D D).mapIso e.unitIso.symm
  invHomIso := by
    change (kanNerveFunctorHomEmbedding E E).obj (e.inverse ⋙ e.functor) ≅
      (kanNerveFunctorHomEmbedding E E).obj (𝟭 E)
    exact (kanNerveFunctorHomEmbedding E E).mapIso e.counitIso

/-- 概要：通常の同値関手の nerve は元の quasicategory の同値。
方針：単位と余単位の自然同型を h Fun の指定同型へ写す。
規約：同じ宇宙の対象・図式・頂点を固定する。
使われ方：B5 の錐の族と普遍性の比較。 -/
lemma kanNerveMap_isQCatEquivalence (F :
    D ⥤ E) [F.IsEquivalence] : IsQCatEquivalence (nerveMap F) :=
  (kanNerveQCatEquivalence F.asEquivalence).isQCatEquivalence

end SerrePositivity.InfinityCategories.F1B
