module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeCompositeDown
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoDownHorizontalTransport

/-!
概要：元の native 二射の合成比較の下降を、元の二つの値比較の前後合成として表示する。
方針：元の水平合成を指定値のまま下降し、合成比較の終端表示だけを補正する。
規約：既存の値比較を保持。使われ方：小宇宙の可換式を四射の脚の整合へ変換する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B D E : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u})
  (H : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ SpaceInfinity.{u})
  (a : smallLeftUnstraightening F ⟶ smallLeftUnstraightening G)
  (b : smallLeftUnstraightening G ⟶ smallLeftUnstraightening H)

/-- 元の合成比較の下降は元の二つの値比較の水平合成そのものである。 -/
lemma coherentTotalMapNativeCompositeDownIso_eq_whisker :
    coherentTotalMapNativeCompositeDownIso F G H a b =
      (coherentTotalMapNativeValueDownIso F G a).postcomp
        (coherentTotalMapNativeValueDown G H b) ≪≫
      (coherentTotalMapNativeValueDownIso G H b).precomp (coherentTotalVertexMap F G a) := by
  let e := coherentTotalMapNativeValueIso F G a
  let d := coherentTotalMapNativeValueIso G H b
  let raw := e.postcomp (coherentTotalMapNativeValue G H b) ≪≫
    d.precomp ((SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G a))
  let P := functorSpaceDown.{u, u + 1}
    (spaceInfinityObject (coherentDiagramTotalVertex F)).obj
    (spaceInfinityObject (coherentDiagramTotalVertex H)).obj
  have hs : coherentTotalMapNativeValue F G a ≫ coherentTotalMapNativeValue G H b =
      (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTotalMapNativeValueDown F G a ≫ coherentTotalMapNativeValueDown G H b) := by
    rw [Functor.map_comp, coherentTotalMapNativeValueDown_lift,
      coherentTotalMapNativeValueDown_lift]
  let ht := ((SSet.uliftFunctor.{u + 1, u}).map_comp
    (coherentTotalVertexMap F G a) (coherentTotalVertexMap G H b)).symm
  have hh : functorIsoDown (functorIsoOfEq raw hs ht) =
      (coherentTotalMapNativeValueDownIso F G a).postcomp
        (coherentTotalMapNativeValueDown G H b) ≪≫
      (coherentTotalMapNativeValueDownIso G H b).precomp (coherentTotalVertexMap F G a) := by
    exact functorIsoDown_horizontal_ofEq e d
      (coherentTotalMapNativeValueDown_lift F G a).symm
      (coherentTotalMapNativeValueDown_lift G H b).symm
  have hm := functorIsoDown_ofEq_heq_mapIso
    (f := coherentTotalMapNativeValueDown F G a ≫ coherentTotalMapNativeValueDown G H b)
    (g := coherentTotalVertexMap F G a ≫ coherentTotalVertexMap G H b) raw hs ht
  have hu : HEq (P.mapIso (coherentTotalMapNativeCompositeIso F G H a b))
      (P.mapIso raw) := mapIso_functorIsoOfEq_heq P raw rfl ht
  apply eq_of_heq
  exact (coherentTotalMapNativeCompositeDownIso_heq_map F G H a b).trans
    (hu.trans ((heq_of_eq hh.symm).trans hm).symm)

end SerrePositivity.InfinityCategories.F2
