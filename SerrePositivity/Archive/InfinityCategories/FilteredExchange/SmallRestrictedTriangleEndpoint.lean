module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NormalizedRestrictedTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallTriangleRelativeRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorOverPreTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DownVertexIsoComparison

/-!
概要：小さい実際の三角形比較を同じ二 prism の局所指定比較の下降へ接続する。
方針：局所比較の両端を揃えた等式を、底の等式移送と標的の縮小後に下降する。
規約：元の全二単体と指定同型を保持。使われ方：各点の native 錐と模型比較の整合。
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

/-- 同じ二 prism の局所指定比較を底の移送・標的の縮小後に元の宇宙へ戻す。 -/
def smallRestrictedTriangleEndpointIso :=
  let m := smallUnstraighteningSourceRestriction F s
  let q := (smallUnstraighteningSourceRelativeIso J
    (s ≫ smallLeftUnstraighteningProjection F)).inv
  downVertexIso (VertexIso.map
    (normalizedRestrictedTriangleIso F G J x y T.diagonal
      T.diagram T.first T.second T.long m.left)
    (eqToHom (congrArg (relativeFunctorSpace (leftUnstraighteningProjection J)) m.w) ≫ q))

/-- 小さい実際の三角形比較の制限は同じ局所指定比較の下降と一致する。 -/
lemma coherentSmallTriangleRelativeIso_pre_heq_endpoint :
    HEq
      (VertexIso.map (coherentTransformationTriangleRelativeIso F G J x y T)
        (relativeFunctorPre (smallLeftUnstraighteningProjection J)
          (smallLeftUnstraighteningProjection F) s))
      (smallRestrictedTriangleEndpointIso F G J x y T s) := by
  let m := smallUnstraighteningSourceRestriction F s
  let q := (smallUnstraighteningSourceRelativeIso J
    (s ≫ smallLeftUnstraighteningProjection F)).inv
  let t := eqToHom (congrArg (relativeFunctorSpace (leftUnstraighteningProjection J)) m.w)
  let e := unstraighteningTriangleRelativeVertexIso F G J x y T.diagonal
    T.diagram T.first T.second T.long
  have hOver : relativeFunctorOverPre (leftUnstraighteningProjection J) m =
      relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        m.left ≫ t :=
    relativeFunctorOverPre_eq_pre_transport (leftUnstraighteningProjection J)
      (leftUnstraighteningProjection F) _ m.left m.w
  have hm := downVertexIso_map_comp_heq e
    (relativeFunctorOverPre (leftUnstraighteningProjection J) m) q
    (relativeFunctorPre (leftUnstraighteningProjection J) (leftUnstraighteningProjection F) m.left)
    (t ≫ q) (by rw [hOver, Category.assoc])
  have h := (coherentSmallTriangleRelativeIso_pre F G J x y T s).trans hm
  rw [unstraighteningTriangleRelativeVertexIso_pre_eq F G J x y T.diagonal
    T.diagram T.first T.second T.long m.left] at h
  exact h

end SerrePositivity.InfinityCategories.F2
