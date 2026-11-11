module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoMapTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoWhiskerVertexMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の全空間の指定比較を縮小すると、同じ前後合成の像を宇宙下降した値になる。
方針：元の下降前の端点補正だけを除き、前後合成と同じ射の像を照合する。
規約：指定値を再選択しない。使われ方：小さい三角形と元の全空間三角形の値の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  {f g : leftUnstraightening F ⟶ leftUnstraightening G} (e : FunctorIso f g)
local notation "p" => Iso.hom (smallLeftUnstraighteningIso F)
local notation "q" => Iso.inv (smallLeftUnstraighteningIso G)

/-- 元の縮小比較は、同じ全空間同型の前後合成と宇宙下降の同じ像。 -/
lemma smallUnstraighteningFunctorIso_heq_down_image :
    HEq (smallUnstraighteningFunctorIso F G e)
      (downVertexIso (VertexIso.map e
        ((pre p).app (leftUnstraightening G) ≫
          (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map q ≫
        (uliftFunctorSpaceIso.{u, u + 1}
          (smallLeftUnstraightening F) (smallLeftUnstraightening G)).inv))) := by
  let K := (pre p).app (leftUnstraightening G) ≫
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map q
  let U := (uliftFunctorSpaceIso.{u, u + 1}
    (smallLeftUnstraightening F) (smallLeftUnstraightening G)).inv
  have hm : HEq ((e.precomp p).postcomp q) (VertexIso.map e K) :=
    (heq_of_eq (functorIso_precomp_postcomp e p q)).trans
      (functorIso_whisker_vertexMap_heq e p q).symm
  have he := vertexIso_map_heq_of_heq ((e.precomp p).postcomp q)
    (VertexIso.map e K) rfl rfl hm U
  have hd := downVertexIso_heq_of_heq _ _ rfl rfl he
  rw [vertexIso_map_comp] at hd
  unfold smallUnstraighteningFunctorIso
  refine (functorIsoDown_ofEq_heq_mapIso
    (X := smallLeftUnstraightening F) (Y := smallLeftUnstraightening G)
    ((e.precomp p).postcomp q) (smallSimplicialMap_ulift.{u, u + 1} f).symm
    (smallSimplicialMap_ulift.{u, u + 1} g).symm).trans ?_
  rw [functorSpaceDown_mapIso]
  exact hd

end SerrePositivity.InfinityCategories.F2
