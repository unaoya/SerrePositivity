module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallRestrictedEndpointVertex
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.IsoEndpointNormalization

/-!
概要：局所三角形比較の下降後の両端を元の小さい実頂点へ正規化する。
方針：縮小と制限の頂点式と合成の厳密な頂点式を指定比較へ適用する。
規約：元の指定比較を保持。使われ方：同じ fiber の作用への局所比較の移送。
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
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y)
  (s : C ⟶ smallLeftUnstraightening F)
local notation "P" => relativeFunctorPre (smallLeftUnstraighteningProjection J)
  (smallLeftUnstraighteningProjection F) s
local notation "c" => smallRestrictedTriangleEndpointIso F G J x y T s

/-- 同じ局所比較を下降後の元の小さい実頂点を両端とする指定同型にする。 -/
def normalizeSmallTriangleEndpointIso
    (e : VertexIso
      (smallRestrictedEndpointVertex F J (leftUnstraighteningMappingVertexMap F J T.diagonal).val
        (leftUnstraighteningMappingVertexMap F J T.diagonal).property s)
      (smallRestrictedEndpointVertex F J
        ((leftUnstraighteningMappingVertexMap F G x).val ≫
          (leftUnstraighteningMappingVertexMap G J y).val)
        (coherentTransformationMappingComposite_projection F G J x y) s)) :
    VertexIso ((P).app (Opposite.op ⦋0⦌) (coherentTransformationRelativeVertex F J T.diagonal))
      ((P).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex (smallLeftUnstraighteningProjection J)
          (smallLeftUnstraighteningProjection F)
          (coherentTransformationTotalMap F G x ≫ coherentTransformationTotalMap G J y)
          (by rw [Category.assoc, coherentTransformationTotalMap_projection,
            coherentTransformationTotalMap_projection]))) := by
  have hs := smallRestrictedEndpointVertex_eq F J
    (leftUnstraighteningMappingVertexMap F J T.diagonal).val
    (leftUnstraighteningMappingVertexMap F J T.diagonal).property s
  have ht := (smallRestrictedEndpointVertex_eq F J
    ((leftUnstraighteningMappingVertexMap F G x).val ≫
      (leftUnstraighteningMappingVertexMap G J y).val)
    (coherentTransformationMappingComposite_projection F G J x y) s).trans
      (congrArg (fun v => (P).app (Opposite.op ⦋0⦌) v)
        (coherentTransformationComposite_relativeVertex F G J x y))
  exact (eqToIso (congrArg SSet.HomotopyCategory.mk hs)).symm ≪≫ e ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk ht)

/-- 同じ局所比較を下降後の元の小さい実頂点へ正規化する。 -/
def normalizedSmallTriangleEndpointIso :=
  normalizeSmallTriangleEndpointIso F G J x y T s c

/-- 下降後の両端の正規化を外しても同じ局所指定比較になる。 -/
lemma normalizedSmallTriangleEndpointIso_heq :
    HEq (normalizedSmallTriangleEndpointIso F G J x y T s) c := by
  unfold normalizedSmallTriangleEndpointIso normalizeSmallTriangleEndpointIso
  dsimp only
  exact iso_endpoints_heq _ _ _

/-- 小さい実際の三角形比較の制限は、同じ局所比較の正規化と指定値まで等しい。 -/
lemma coherentSmallTriangleRelativeIso_pre_eq_endpoint :
    VertexIso.map (coherentTransformationTriangleRelativeIso F G J x y T) P =
      normalizedSmallTriangleEndpointIso F G J x y T s := by
  exact eq_of_heq ((coherentSmallTriangleRelativeIso_pre_heq_endpoint F G J x y T s).trans
    (normalizedSmallTriangleEndpointIso_heq F G J x y T s).symm)

/-- 同じ指定同型の小さい両端の補正は、任意の後合成の指定像の値を保持する。 -/
lemma normalizeSmallTriangleEndpointIso_map_heq {L : SSet.{u}}
    (e : VertexIso
      (smallRestrictedEndpointVertex F J (leftUnstraighteningMappingVertexMap F J T.diagonal).val
        (leftUnstraighteningMappingVertexMap F J T.diagonal).property s)
      (smallRestrictedEndpointVertex F J
        ((leftUnstraighteningMappingVertexMap F G x).val ≫
          (leftUnstraighteningMappingVertexMap G J y).val)
        (coherentTransformationMappingComposite_projection F G J x y) s))
    (f : relativeFunctorSpace (smallLeftUnstraighteningProjection J)
      (s ≫ smallLeftUnstraighteningProjection F) ⟶ L) :
    HEq (VertexIso.map (normalizeSmallTriangleEndpointIso F G J x y T s e) f)
      (VertexIso.map e f) := by
  unfold normalizeSmallTriangleEndpointIso
  dsimp only
  exact isoNormalizeEndpoints_map_heq (SSet.mapHomotopyCategory f) e _ _

end SerrePositivity.InfinityCategories.F2
