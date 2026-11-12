module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSubdivision
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.JoinSelfOpposite

/-!
概要：edgewise の重みは反転に関して自然に自己同型となる。
方針：既存の join の反転同型と標準単体の二重反転同型を合成する。
規約：Stable のファイルは参照のみで、モデル構造や ∞ 圏の極限は用いない。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、Corollary 5.6.0.6（Tag 028T）、自然な反転比較の左射影の同値。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：edgewise の各重みの反転を元の重みへ戻す同型。
方針：join の反転で因子を交換し、右因子の二重反転を消去する。
規約：始域は重みの単体集合としての反転。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、edgewise の双対写像の各次数の定義。 -/
noncomputable def edgewiseWeightReverseIso (n : SimplexCategory) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.obj n).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.obj n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.joinSelfOppositeIso (stdSimplex.obj n)

/-- 概要：重みの反転同型は単体圏の射と可換。
方針：join の反転の二因子の自然性と二重反転同型の自然性を使う。
規約：α は任意の面・退化とその合成。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、双対写像の単体的な自然性。 -/
lemma edgewiseWeightReverse_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map α) ≫ (edgewiseWeightReverseIso n).hom =
      (edgewiseWeightReverseIso m).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.joinSelfOpposite_naturality (stdSimplex.map α)

/-- 概要：重みの逆反転同型も単体圏の射と可換。
方針：反転同型の自然性に逆同型を合成し、往復を消去する。
規約：双対写像ではこちらの向きを使う。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、重みからの射を反転する際の前合成。 -/
lemma edgewiseWeightReverse_inv_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.{u}.map α ≫ (edgewiseWeightReverseIso n).inv =
      (edgewiseWeightReverseIso m).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.joinSelfOpposite_inv_naturality (stdSimplex.map α)

/-- 概要：重みを逆反転すると右包含は元の左包含の反転になる。
方針：join の右包含と因子の射の可換性を使い、既存の join の反転の包含の式へ戻す。
規約：標準単体の二重反転の逆を始域へ合成する。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、左端射影と反転後の右端射影の照合。 -/
lemma edgewiseWeightReverse_inv_inr (n : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (stdSimplex.obj n).op (stdSimplex.obj n) ≫ (edgewiseWeightReverseIso.{u} n).inv =
      (SSet.opFunctorCompOpFunctorIso.app (stdSimplex.obj n)).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n).op (stdSimplex.obj n)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.joinSelfOpposite_inv_inr (stdSimplex.obj n)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
