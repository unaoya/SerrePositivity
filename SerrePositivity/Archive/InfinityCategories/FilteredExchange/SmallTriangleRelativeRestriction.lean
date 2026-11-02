module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallTriangleRelativePresentation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallRelativeVertexRestriction

/-!
概要：小さい全空間の実際の三角形比較の制限を、元の全三角形の同じ比較へ移す。
方針：合成頂点の正規化を外し、相対縮小と始域制限の交換式を適用する。
規約：元の三辺・全二単体・指定同型を保持。使われ方：各点の錐と全空間比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y)
local notation "e" => unstraighteningTriangleRelativeVertexIso F G J x y T.diagonal
  T.diagram T.first T.second T.long
local notation "hp" => coherentTransformationMappingComposite_projection F G J x y

/-- 小さい実際の三角形比較の制限は同じ全三角形の指定相対比較を制限した値の下降。 -/
lemma coherentSmallTriangleRelativeIso_pre {C : SSet.{u}}
    (s : C ⟶ smallLeftUnstraightening F) :
    HEq
      (VertexIso.map (coherentTransformationTriangleRelativeIso F G J x y T)
        (relativeFunctorPre (smallLeftUnstraighteningProjection J)
          (smallLeftUnstraighteningProjection F) s))
      (downVertexIso
        (VertexIso.map (VertexIso.map e
          (relativeFunctorOverPre (leftUnstraighteningProjection J)
            (smallUnstraighteningSourceRestriction F s)))
          (smallUnstraighteningSourceRelativeIso J
            (s ≫ smallLeftUnstraighteningProjection F)).inv)) := by
  let e' := smallUnstraighteningRelativeVertexIso F J
    (leftUnstraighteningMappingVertexMap F J T.diagonal).property hp e
  have hm := vertexIso_map_heq_of_heq (coherentTransformationTriangleRelativeIso F G J x y T) e'
    rfl (coherentTransformationComposite_relativeVertex F G J x y).symm
    (coherentTriangleRelativeIso_heq_small F G J x y T)
    (relativeFunctorPre (smallLeftUnstraighteningProjection J)
      (smallLeftUnstraighteningProjection F) s)
  exact hm.trans (smallRelativeVertexIso_pre_heq_restrict_down F J
    (leftUnstraighteningMappingVertexMap F J T.diagonal).property hp e s)

end SerrePositivity.InfinityCategories.F2
