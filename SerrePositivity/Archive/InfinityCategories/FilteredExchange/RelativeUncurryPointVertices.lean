module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningConstantVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyVertices

/-!
概要：元の定値変換の族とその合成を一点で評価して実際の底上の射へ戻す。
方針：相対 curry/uncurry の往復と既存の実頂点の等式を合成する。
規約：元の射と指定した点を保持。使われ方：局所延長比較の両端の実頂点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対 uncurry の後で curry すると元の全パラメータの族を回収する。 -/
lemma relativeFunctorCurry_uncurry {A E B K : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f : K ⟶ relativeFunctorSpace p a) :
    relativeFunctorCurry (relativeFunctorUncurry f) (relativeFunctorUncurry_projection f) = f := by
  apply relativeFunctorUncurry_injective
  exact relativeFunctorUncurry_curry _ _

/-- 元の相対族の一点での uncurry の実頂点は同じ族の実際の値。 -/
lemma relativeFunctorUncurry_point_vertex {A E B K : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f : K ⟶ relativeFunctorSpace p a) (k : K _⦋0⦌) :
    relativeFunctorVertex p a (lift (𝟙 A) (SSet.const k) ≫ relativeFunctorUncurry f)
      (by rw [Category.assoc, relativeFunctorUncurry_projection, ← Category.assoc,
        lift_fst, Category.id_comp]) = f.app (Opposite.op ⦋0⦌) k := by
  have h := relativeFunctorCurry_vertex p a (relativeFunctorUncurry f)
    (relativeFunctorUncurry_projection f) k
  rw [relativeFunctorCurry_uncurry] at h
  exact h.symm

/-- 定値変換の元の比較射の一点評価は、元の底上の射そのもの。 -/
lemma unstraighteningUncurryConst_point {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (k : K _⦋0⦌) :
    lift (𝟙 (leftUnstraightening F)) (SSet.const k) ≫
        relativeFunctorUncurry ((SSet.const x : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap F G) =
      (leftUnstraighteningMappingVertexMap F G x).val := by
  apply functorVertex_injective
  exact congrArg Subtype.val
    ((relativeFunctorUncurry_point_vertex _ _ _ k).trans
      (unstraighteningMappingConst_vertex F G x k))

/-- 元の定値二変換の族の合成の一点評価は同じ二つの底上の射の合成。 -/
lemma unstraighteningUncurryConstComposite_point {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌) (k : K _⦋0⦌) :
    lift (𝟙 (leftUnstraightening F)) (SSet.const k) ≫
      (lift (relativeFunctorUncurry ((SSet.const x : K ⟶ _) ≫
          leftUnstraighteningMappingSpaceMap F G)) (snd (leftUnstraightening F) K) ≫
        relativeFunctorUncurry ((SSet.const y : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap G J)) =
      (leftUnstraighteningMappingVertexMap F G x).val ≫
        (leftUnstraighteningMappingVertexMap G J y).val := by
  let d := lift ((SSet.const x : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap F G)
    ((SSet.const y : K ⟶ _) ≫ leftUnstraighteningMappingSpaceMap G J) ≫
      relativeFunctorComposition (Over.mk (leftUnstraighteningProjection F))
        (Over.mk (leftUnstraighteningProjection G)) (Over.mk (leftUnstraighteningProjection J))
  have hd : relativeFunctorUncurry d =
      lift (relativeFunctorUncurry ((SSet.const x : K ⟶ _) ≫
        leftUnstraighteningMappingSpaceMap F G)) (snd (leftUnstraightening F) K) ≫
        relativeFunctorUncurry ((SSet.const y : K ⟶ _) ≫
          leftUnstraighteningMappingSpaceMap G J) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← hd]
  apply functorVertex_injective
  exact congrArg Subtype.val
    ((relativeFunctorUncurry_point_vertex _ _ d k).trans
      (unstraighteningMappingConstComposite_vertex F G J x y k))

end SerrePositivity.InfinityCategories.F2
