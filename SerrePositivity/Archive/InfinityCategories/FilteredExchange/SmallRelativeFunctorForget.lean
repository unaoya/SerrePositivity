module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningFunctorIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningRelativeVertex

/-!
概要：相対写像空間の縮小と忘却は、同じ全空間の縮小操作と全次数で可換。
方針：元の縮小同型の実際の前後合成と宇宙下降を各単体で計算する。
規約：元の全族の射を保持。使われ方：指定三角形の小さい比較と全空間比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の相対縮小同型の忘却は、元の全空間の前後合成と宇宙下降の同じ合成射。 -/
lemma smallUnstraighteningRelativeIso_inv_forget {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    (smallLeftUnstraighteningRelativeFunctorIso F G).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberι ((ihom (smallLeftUnstraightening F)).map
          (smallLeftUnstraighteningProjection G))
          (functorVertex (smallLeftUnstraighteningProjection F))) =
    vertexFiberι ((ihom (leftUnstraightening F)).map (leftUnstraighteningProjection G))
      (functorVertex (leftUnstraighteningProjection F)) ≫
      (pre (smallLeftUnstraighteningIso F).hom).app (leftUnstraightening G) ≫
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map
        (smallLeftUnstraighteningIso G).inv ≫
      (uliftFunctorSpaceIso.{u, u + 1}
        (smallLeftUnstraightening F) (smallLeftUnstraightening G)).inv := by
  apply SSet.hom_ext
  intro k
  apply ConcreteCategory.hom_ext
  intro v
  rfl

end SerrePositivity.InfinityCategories.F2
