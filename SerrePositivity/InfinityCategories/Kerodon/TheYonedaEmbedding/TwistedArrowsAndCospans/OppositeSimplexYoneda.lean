module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints

/-!
概要：反転した標準単体からの射を二重反転経由で Yoneda 表示する計算。
方針：零からの頂点写像ではなく任意次数の普遍単体で両辺を比較する。
規約：二重反転の同型と標準単体の反転同型を区別する。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、edgewise の双対写像と左右射影の照合。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：二重反転の逆を始域へ合成した反転射の Yoneda 単体は、標準反転による単体の反転。
方針：標的の各次数の反転の同値で比較し、普遍単体の頂点の二重反転を消去する。
規約：n は任意の単体圏の対象。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、双対後の右射影と元の左射影の等式。 -/
lemma oppositeSimplex_yoneda {K : SSet.{u}} (n : SimplexCategory)
    (g : (stdSimplex.obj n).op ⟶ K) :
    SSet.yonedaEquiv ((SSet.opFunctorCompOpFunctorIso.app (stdSimplex.obj n)).inv ≫
      SSet.opFunctor.map g) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv ((stdSimplex.opIso n).inv ≫ g)) := by
  apply SSet.opObjEquiv.injective
  change g.app (Opposite.op n) (SSet.opObjEquiv.symm (stdSimplex.objEquiv.symm (𝟙 n))) =
    g.app (Opposite.op n) (SSet.yonedaEquiv (stdSimplex.opIso n).inv)
  apply congrArg (g.app (Opposite.op n))
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro i
  change i = i.rev.rev
  rw [Fin.rev_rev]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
