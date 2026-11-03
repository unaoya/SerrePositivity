module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallUnstraighteningFunctorIsoImage

/-!
概要：元の全空間間の全 Hom を、同じ縮小同型による小さい全 Hom の持ち上げへ写す。
方針：元の前後合成と内部 Hom の宇宙移送を同じ順で保持する。
規約：全次数の射と実頂点を保持。使われ方：縮小した模型比較の持ち上げの照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の二つの全空間の縮小同型を用いる、同じ全 Hom の指定縮小射。 -/
def smallTotalHomShrink :=
  (pre (smallLeftUnstraighteningIso F).hom).app (leftUnstraightening G) ≫
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map
      (smallLeftUnstraighteningIso G).inv ≫
    (uliftFunctorSpaceIso.{u, u + 1}
      (smallLeftUnstraightening F) (smallLeftUnstraightening G)).inv

/-- 元の全 Hom の縮小射は、元の射を縮小した同じ頂点を厳密に回収する。 -/
lemma smallTotalHomShrink_vertex (f : leftUnstraightening F ⟶ leftUnstraightening G) :
    (smallTotalHomShrink F G).app (Opposite.op ⦋0⦌) (functorVertex f) =
      ULift.up (functorVertex (smallLeftUnstraighteningOverMap F G f)) := by
  change (uliftFunctorSpaceIso.{u, u + 1}
    (smallLeftUnstraightening F) (smallLeftUnstraightening G)).inv.app (Opposite.op ⦋0⦌)
    (functorVertex ((smallLeftUnstraighteningIso F).hom ≫ f ≫
      (smallLeftUnstraighteningIso G).inv)) = _
  exact congrArg (fun k => (uliftFunctorSpaceIso.{u, u + 1}
    (smallLeftUnstraightening F) (smallLeftUnstraightening G)).inv.app (Opposite.op ⦋0⦌)
      (functorVertex k)) (smallSimplicialMap_ulift.{u, u + 1} f).symm

end SerrePositivity.InfinityCategories.F2
