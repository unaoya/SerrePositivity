module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeValue

/-!
概要：元の二つの native 余極限写像の値の合成を具体的頂点射の合成へ比較する。
方針：二つの指定値比較を前後合成して続ける。
規約：元の二比較を保持。使われ方：cospan 錐の左右の合成の同時照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B C D : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u})
  (H : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
  (b : smallLeftUnstraightening G ⟶ smallLeftUnstraightening H)

/-- 概要：native な二射の値の合成は元の具体的な二頂点射の合成へ指定同型を持つ。
方針：元の二つの比較の whisker を合成し、持ち上げの合成式だけ移す。
規約：指定値の同型。使われ方：元の四辺の比較と可換 path の同時照合。 -/
def coherentTotalMapNativeCompositeIso :
    FunctorIso (coherentTotalMapNativeValue F G a ≫ coherentTotalMapNativeValue G H b)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (coherentTotalVertexMap F G a ≫ coherentTotalVertexMap G H b)) := by
  have e := (coherentTotalMapNativeValueIso F G a).postcomp (coherentTotalMapNativeValue G H b)
  have d := (coherentTotalMapNativeValueIso G H b).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a))
  exact functorIsoOfEq (e ≪≫ d) rfl ((SSet.uliftFunctor.{u + 1, u}).map_comp _ _).symm

end SerrePositivity.InfinityCategories.F2
