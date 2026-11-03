module

public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorComposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingInvertible
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativeFunctorCompositionVertex

/-!
概要：定値パラメータの実際の比較頂点と合成を元の底上の射で表示する。
方針：零単体で定値写像を評価し、相対豊穣合成の頂点式へ渡す。
規約：元の比較射を保持。使われ方：三角形比較の成分の両端の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 定値写像の零単体での値は指定した元の頂点。 -/
lemma constMap_vertex_value {X A : SSet.{u}} (v : X _⦋0⦌) (a : A _⦋0⦌) :
    (SSet.const v : A ⟶ X).app (Opposite.op ⦋0⦌) a = v := by
  change X.map _ v = v
  rw [show (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = 𝟙 (Opposite.op ⦋0⦌) from
    Subsingleton.elim _ _, X.map_id]
  rfl

/-- 元の定値変換の族の実際の比較頂点は同じ底上の射の相対頂点。 -/
lemma unstraighteningMappingConst_vertex {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (k : K _⦋0⦌) :
    ((SSet.const x : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap F G).app (Opposite.op ⦋0⦌) k =
      relativeFunctorVertex (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)
        (leftUnstraighteningMappingVertexMap F G x).val
        (leftUnstraighteningMappingVertexMap F G x).property := by
  rw [SSet.const_comp]
  rw [constMap_vertex_value]
  exact (leftUnstraighteningMappingVertexMap_vertex F G x).symm

/-- 二つの元の定値変換の族の相対合成の頂点は同じ二射の合成の相対頂点。 -/
lemma unstraighteningMappingConstComposite_vertex {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌) (k : K _⦋0⦌) :
    (lift ((SSet.const x : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap F G)
      ((SSet.const y : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap G J) ≫
        relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
          (Over.mk (leftUnstraighteningProjection G))
          (Over.mk (leftUnstraighteningProjection J))).app (Opposite.op ⦋0⦌) k =
      relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        ((leftUnstraighteningMappingVertexMap F G x).val ≫
          (leftUnstraighteningMappingVertexMap G J y).val)
        (by rw [Category.assoc, (leftUnstraighteningMappingVertexMap G J y).property,
          (leftUnstraighteningMappingVertexMap F G x).property]) := by
  change (relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
    (Over.mk (leftUnstraighteningProjection G)) (Over.mk (leftUnstraighteningProjection J))).app
      (Opposite.op ⦋0⦌)
        (((SSet.const x : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap F G).app _ k,
         ((SSet.const y : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap G J).app _ k) = _
  rw [unstraighteningMappingConst_vertex, unstraighteningMappingConst_vertex]
  exact relativeFunctorComposition_vertex _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
