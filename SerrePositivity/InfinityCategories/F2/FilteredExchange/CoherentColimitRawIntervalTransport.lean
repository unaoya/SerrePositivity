module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawInterval
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalMappingFamilyEndpointTransport

/-!
概要：元の余錐頂点と native 頂点で表示した同じ指定余極限辺の全区間族を照合する。
方針：元の終点等式だけを使い、同じ一単体の区間写像族を保持する。
規約：元の辺・族を再選択しない。使われ方：下側輸送因子の raw/native 表示の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- raw/native の二区間族は、元の同じ余極限辺の終点だけの等式移送。 -/
lemma coherentColimitRawIntervalFamily_heq_native (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F G) :
    HEq (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H))
      (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)) := by
  exact intervalMappingVertexFamily_heq_of_target_eq
    (coherentDiagramTotalCocone_vertex G) _ _ rfl

end SerrePositivity.InfinityCategories.F2
