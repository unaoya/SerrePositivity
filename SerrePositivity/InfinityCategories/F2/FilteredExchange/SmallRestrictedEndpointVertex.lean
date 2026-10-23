module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SmallRestrictedTriangleEndpoint

/-!
概要：底の移送と標的の縮小後の局所終点を元の小さい相対頂点へ揃える。
方針：相対縮小と始域制限の交換式を元の実頂点へ適用し、ULift を外す。
規約：元の底上の射を保持。使われ方：局所指定比較の下降後の両端の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (f : leftUnstraightening F ⟶ leftUnstraightening G)
  (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
  (s : C ⟶ smallLeftUnstraightening F)

/-- 同じ局所終点を底の移送と標的の縮小後に元の宇宙へ降ろした実頂点。 -/
def smallRestrictedEndpointVertex :
    (relativeFunctorSpace (smallLeftUnstraighteningProjection G)
      (s ≫ smallLeftUnstraighteningProjection F)) _⦋0⦌ :=
  let m := smallUnstraighteningSourceRestriction F s
  let q := (smallUnstraighteningSourceRelativeIso G
    (s ≫ smallLeftUnstraighteningProjection F)).inv
  ((eqToHom (congrArg (relativeFunctorSpace (leftUnstraighteningProjection G)) m.w) ≫ q).app _
    ((relativeFunctorPre (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
      m.left).app _ (relativeFunctorVertex _ _ f hf))).down

/-- 下降後の実頂点は元の小さい全空間射の同じ始域制限の実頂点。 -/
lemma smallRestrictedEndpointVertex_eq :
    smallRestrictedEndpointVertex F G f hf s =
      (relativeFunctorPre (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningProjection F) s).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex _ _ (smallLeftUnstraighteningOverMap F G f)
          (smallLeftUnstraighteningOverMap_projection F G f hf)) := by
  let m := smallUnstraighteningSourceRestriction F s
  let q := (smallUnstraighteningSourceRelativeIso G
    (s ≫ smallLeftUnstraighteningProjection F)).inv
  let t := eqToHom (congrArg (relativeFunctorSpace (leftUnstraighteningProjection G)) m.w)
  let P := relativeFunctorPre (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningProjection F) s
  have hOver : relativeFunctorOverPre (leftUnstraighteningProjection G) m =
      relativeFunctorPre (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        m.left ≫ t :=
    relativeFunctorOverPre_eq_pre_transport (leftUnstraighteningProjection G)
      (leftUnstraighteningProjection F) _ m.left m.w
  have hs := smallRelativeFunctorIso_inv_pre F G s
  rw [hOver] at hs
  have hv := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (relativeFunctorVertex _ _ f hf)) hs.symm
  have ht : ((smallLeftUnstraighteningRelativeFunctorIso F G).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map P).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex _ _ f hf) =
      ULift.up ((P).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex _ _ (smallLeftUnstraighteningOverMap F G f)
          (smallLeftUnstraighteningOverMap_projection F G f hf))) := by
    change ((SSet.uliftFunctor.{u + 1, u}).map P).app _
      ((smallLeftUnstraighteningRelativeFunctorIso F G).inv.app _
        (relativeFunctorVertex _ _ f hf)) = _
    rw [smallUnstraighteningRelativeIso_inv_vertex]
    rfl
  exact congrArg ULift.down (hv.trans ht)

end SerrePositivity.InfinityCategories.F2
