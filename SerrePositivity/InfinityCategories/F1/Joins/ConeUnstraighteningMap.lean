module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeSectionsMap
public import SerrePositivity.InfinityCategories.F1.Diagrams.ConstantSourceSectionMap
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorUnitHom

/-!
概要：元の錐の標準変換が与える、定値 unstraightening からの実際の底上の射を保持する。
方針：相対関手の頂点の全単射で射を取り出し、同じ全切断写像との一致を示す。
規約：元の錐・変換・底上の射を選び直さない。
使われ方：元の相対合成を全切断の後合成へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の錐の標準変換の像を表す、同じ定値全空間からの底上の射。 -/
def coneUnstraighteningArrow (c : JoinCone F) :
    Over.mk (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _)) ⟶
      Over.mk (leftUnstraighteningProjection F) :=
  (overHomEquivSubtype _ _).symm ((relativeFunctorVertexEquiv _ _).symm
    ((leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) F).app (Opposite.op ⦋0⦌)
      (coneTransformationVertex c)))

/-- 同じ底上の射の相対頂点は元の標準変換の像そのもの。 -/
lemma coneUnstraighteningArrow_vertex (c : JoinCone F) :
    relativeFunctorVertex (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection (SSet.const c.vertex))
      (coneUnstraighteningArrow c).left (coneUnstraighteningArrow c).w =
        (leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) F).app (Opposite.op ⦋0⦌)
          (coneTransformationVertex c) :=
  (relativeFunctorVertexEquiv _ _).apply_symm_apply _

/-- 元の全切断写像は、同じ底上の射を全切断へ curry した射と厳密に一致する。 -/
lemma coneSectionsMap_eq_sectionMap (c : JoinCone F) :
    coneSectionsMap c = constantSourceSectionMap F c.vertex
      (coneUnstraighteningArrow c).left (coneUnstraighteningArrow c).w := by
  apply functorVertex_injective
  rw [coneSectionsMap, coneSectionsMapAt_vertex]
  change (constantUnstraighteningSourceRelativeIso F c.vertex).hom.app (Opposite.op ⦋0⦌)
    ((leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) F).app (Opposite.op ⦋0⦌)
      (coneTransformationVertex c)) = _
  rw [← coneUnstraighteningArrow_vertex, constantSourceSectionMap_vertex]

/-- 任意のパラメータで、同じ標準変換の定値族の評価は同じ底上の射の定値族。 -/
lemma coneUnstraighteningArrow_const_evaluation {T : SSet.{u + 1}} (c : JoinCone F) :
    relativeFunctorUncurry ((SSet.const (coneTransformationVertex c) : T ⟶ _) ≫
      leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) F) =
        fst (leftUnstraightening (SSet.const c.vertex : B ⟶ _)) T ≫
          (coneUnstraighteningArrow c).left := by
  rw [relativeFunctorUncurry, SSet.const_comp, SSet.const_comp]
  have h := congrArg Subtype.val (coneUnstraighteningArrow_vertex c)
  change functorVertex (coneUnstraighteningArrow c).left = _ at h
  change uncurry (SSet.const
    (((leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) F).app (Opposite.op ⦋0⦌)
      (coneTransformationVertex c)).val) : T ⟶ _) = _
  rw [← h]
  exact uncurry_const_functorVertex _

end SerrePositivity.InfinityCategories
