module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationTriangleRelative
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallRelativeVertexIsoPresentation

/-!
概要：小さい全空間の実際の三角形比較から合成頂点の正規化を外す。
方針：小さい写像の合成等式を相対頂点へ写し、終点の等式移送を除去する。
規約：元の指定比較を保持。使われ方：小宇宙の三角形比較の始域制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定同型の終点を等式で移送しても元の指定値と HEq で一致する。 -/
lemma iso_target_transport_heq {C : Type u} [Category.{u} C]
    {a b c : C} (e : a ≅ b) (h : b = c) : HEq (e ≪≫ eqToIso h) e := by
  cases h
  simp

variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)

/-- 元の二つの底上の全空間射の合成は同じ始域の射影を被覆する。 -/
lemma coherentTransformationMappingComposite_projection :
    ((leftUnstraighteningMappingVertexMap F G x).val ≫
      (leftUnstraighteningMappingVertexMap G J y).val) ≫ leftUnstraighteningProjection J =
        leftUnstraighteningProjection F := by
  rw [Category.assoc, (leftUnstraighteningMappingVertexMap G J y).property,
    (leftUnstraighteningMappingVertexMap F G x).property]

/-- 元の合成を縮小した相対頂点は実際の二つの小さい射の合成の相対頂点。 -/
lemma coherentTransformationComposite_relativeVertex :
    relativeFunctorVertex _ _
      (smallLeftUnstraighteningOverMap F J ((leftUnstraighteningMappingVertexMap F G x).val ≫
        (leftUnstraighteningMappingVertexMap G J y).val))
      (smallLeftUnstraighteningOverMap_projection F J _
        (coherentTransformationMappingComposite_projection F G J x y)) =
    relativeFunctorVertex (smallLeftUnstraighteningProjection J)
      (smallLeftUnstraighteningProjection F)
      (coherentTransformationTotalMap F G x ≫ coherentTransformationTotalMap G J y)
      (by rw [Category.assoc, coherentTransformationTotalMap_projection,
        coherentTransformationTotalMap_projection]) := by
  apply Subtype.ext
  exact congrArg functorVertex
    (smallSimplicialMap_comp.{u, u + 1} (leftUnstraighteningMappingVertexMap F G x).val
      (leftUnstraighteningMappingVertexMap G J y).val)

/-- 実際の小さい三角形比較は元の相対頂点比較の縮小の終点正規化。 -/
lemma coherentTriangleRelativeIso_heq_small
    (T : CoherentTransformationVertexTriangle F G J x y) :
    HEq (coherentTransformationTriangleRelativeIso F G J x y T)
      (smallUnstraighteningRelativeVertexIso F J
        (leftUnstraighteningMappingVertexMap F J T.diagonal).property
        (coherentTransformationMappingComposite_projection F G J x y)
        (unstraighteningTriangleRelativeVertexIso F G J x y T.diagonal
          T.diagram T.first T.second T.long)) := by
  unfold coherentTransformationTriangleRelativeIso
  dsimp only
  exact iso_target_transport_heq _ _

end SerrePositivity.InfinityCategories.F2
