module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceImageMap
public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.PresentableEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.PreservingFunctorSpaces
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor

/-!
概要：元の余錐頂点で正規化した slice 後合成の小余極限保存を示す。
方針：既存の slice 後合成保存と、固定点の厳密同型による保存を合成する。
規約：第一脚の小余極限保存だけを使う。
使われ方：交互可算図式の第一成分の余極限像の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：余極限保存関手の正規化した固定標的 slice 後合成も全小余極限を保存する。
方針：既存の後合成と元の固定点の同型を順に使う。
規約：第二脚や点射の全小余極限保存を仮定しない。
使われ方：fiber の可算交互比較の指定余錐像。 -/
lemma coconeSliceImageMap_preservesSmallColimits {K : SSet.{u + 1}}
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    {D : K ⟶ E} (c : JoinCocone D) (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E)
    (p : E ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (coconeSliceImageMap c p) := by
  exact (sliceOverPostcomp_preservesSmallColimits hE p hp _).comp
    (equivalence_preservesSmallColimits
      (qCatEquivalenceOfIso (eqToIso (congrArg sliceOver (coconeSliceImagePoint_eq c p)))).isQCatEquivalence)

end SerrePositivity.InfinityCategories.F2.Presentable
