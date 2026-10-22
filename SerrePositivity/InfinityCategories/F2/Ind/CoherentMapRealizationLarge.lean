module

public import SerrePositivity.InfinityCategories.F2.Ind.CoherentMapRealization
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexIso

/-!
概要：元の小さい c1 の実現同型を、元の大きい unstraightening の相対 Hom へ移す。
方針：小さい全空間の厳密な比較同型と、写像空間比較の可換式を使う。
規約：指定された変換と指定された相対射を保持し、実現を選び直さない。
使われ方：密度の元の大域評価と底変換自然性との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}}
  (H G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (L : smallLeftUnstraightening H ⟶ smallLeftUnstraightening G)
  (hL : L ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection H)

/-- 元の底上の射を全空間の縮小同型で元の大きい全空間へ戻す。 -/
def coherentRealizationLargeMap : leftUnstraightening H ⟶ leftUnstraightening G :=
  ((smallLeftUnstraighteningIso H).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map L) ≫
    (smallLeftUnstraighteningIso G).hom

include hL in
/-- 同じ全空間の射は元の持ち上げた底の上にある。 -/
lemma coherentRealizationLargeMap_projection :
    coherentRealizationLargeMap H G L ≫ leftUnstraighteningProjection G =
      leftUnstraighteningProjection H := by
  rw [coherentRealizationLargeMap, Category.assoc, smallLeftUnstraighteningIso_projection,
    Category.assoc, ← Functor.map_comp, hL, ← smallLeftUnstraighteningIso_projection,
    Iso.inv_hom_id_assoc]

/-- 小さい相対射の頂点を移すと、元の大きい全空間へ戻した同じ射の頂点。 -/
lemma coherentRealizationLargeMap_vertex :
    (smallLeftUnstraighteningRelativeFunctorIso H G).hom.app (Opposite.op ⦋0⦌)
      (ULift.up (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningProjection H) L hL)) =
    relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection H)
      (coherentRealizationLargeMap H G L) (coherentRealizationLargeMap_projection H G L hL) := by
  change (relativeFunctorOverIso (smallLeftUnstraighteningOverIso H)
    (smallLeftUnstraighteningOverIso G)).hom.app _
      ((uliftRelativeFunctorMap _ _).app _ (ULift.up (relativeFunctorVertex _ _ L hL))) = _
  rw [uliftRelativeFunctorMap_vertex]
  exact relativeFunctorOverIso_vertex (smallLeftUnstraighteningOverIso H)
    (smallLeftUnstraighteningOverIso G) ((SSet.uliftFunctor.{u + 1, u}).map L)
      (by
        change (SSet.uliftFunctor.{u + 1, u}).map L ≫
          (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection G) = _
        rw [← Functor.map_comp, hL]
        rfl)

/-- 元の c1 の実現同型を、元の大きい写像空間比較の像との同型として保持する。 -/
def coherentMapRealizationLargeIso (R : CoherentMapRealization H G L hL) :
    VertexIso
      ((leftUnstraighteningMappingSpaceMap H G).app (Opposite.op ⦋0⦌)
        ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
          (ULift.up R.transformation)))
      (relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection H)
        (coherentRealizationLargeMap H G L) (coherentRealizationLargeMap_projection H G L hL)) := by
  have he := VertexIso.map (uliftVertexIso.{u, u + 1} R.imageIso)
    (smallLeftUnstraighteningRelativeFunctorIso H G).hom
  have hc := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up R.transformation))
    (smallLeftUnstraighteningMappingSpaceMap_comparison H G)
  exact eqToIso (congrArg HomotopyCategory.mk hc.symm) ≪≫ he ≪≫
    eqToIso (congrArg HomotopyCategory.mk (coherentRealizationLargeMap_vertex H G L hL))

end SerrePositivity.InfinityCategories.F2.Ind
