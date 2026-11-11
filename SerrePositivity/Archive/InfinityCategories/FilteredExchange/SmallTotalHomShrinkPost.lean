module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallTotalHomShrink
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UliftPostcomposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.LargeTotalCoconeUnit

/-!
概要：全 Hom の縮小後の後合成・再持ち上げを、元の全空間の同じ後合成へ戻す。
方針：内部 Hom の宇宙移送の自然性と、同じ始域縮小同型の往復を消す。
規約：全次数の射を保持。使われ方：模型三角形の単位による像の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 同じ全 Hom の縮小・後合成・持ち上げの合成射は、元の後合成作用そのもの。 -/
lemma smallTotalHomShrink_post_cancel (Z : SSet.{u}) (w : smallLeftUnstraightening G ⟶ Z) :
    smallTotalHomShrink F G ≫
      (SSet.uliftFunctor.{u + 1, u}).map ((ihom (smallLeftUnstraightening F)).map w) ≫
      (smallUnstraighteningHomIso F Z).inv =
    (ihom (leftUnstraightening F)).map
      ((smallLeftUnstraighteningIso G).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map w) := by
  let p := (smallLeftUnstraighteningIso F).hom
  let s := (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map
    (smallLeftUnstraighteningIso G).inv
  let W := (SSet.uliftFunctor.{u + 1, u}).map w
  let h := (smallLeftUnstraighteningIso G).inv ≫ W
  let U₁ := uliftFunctorSpaceIso.{u, u + 1}
    (smallLeftUnstraightening F) (smallLeftUnstraightening G)
  let U₂ := uliftFunctorSpaceIso.{u, u + 1} (smallLeftUnstraightening F) Z
  let v := (SSet.uliftFunctor.{u + 1, u}).map ((ihom (smallLeftUnstraightening F)).map w)
  let q := (pre (smallLeftUnstraighteningIso F).inv).app ((SSet.uliftFunctor.{u + 1, u}).obj Z)
  change ((pre p).app (leftUnstraightening G) ≫ s ≫ U₁.inv) ≫ v ≫ (U₂.hom ≫ q) = _
  calc
    _ = (pre p).app (leftUnstraightening G) ≫ s ≫ (U₁.inv ≫ v ≫ U₂.hom) ≫ q := by
      simp only [Category.assoc]
    _ = (pre p).app (leftUnstraightening G) ≫ s ≫
        (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map W ≫ q := by
      rw [uliftFunctorSpaceIso_inv_post_hom]
    _ = (pre p).app (leftUnstraightening G) ≫
        (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening F))).map h ≫ q := by
      simp only [s, h, Functor.map_comp, Category.assoc]
    _ = (ihom (leftUnstraightening F)).map h ≫
        (pre p).app ((SSet.uliftFunctor.{u + 1, u}).obj Z) ≫ q := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ q) ((pre p).naturality h).symm
    _ = _ := by
      rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]

end SerrePositivity.InfinityCategories.F2
