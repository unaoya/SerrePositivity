module

public import SerrePositivity.InfinityCategories.F1.FunctorTriangleVertexEvaluation

/-!
概要：同じ大域可逆三角形の族を、元の可逆三角形空間へ持ち上げる。
方針：各頂点で同じ大域二単体を評価し、三辺の可逆性を保持する。
規約：包含後は元の全高次の族そのもの。
使われ方：元の比較三角形の Hom と既存の可逆 path の Hom を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A Y : SSet.{u}} (F : A ⟶ (ihom (Δ[2] : SSet.{u})).obj Y)
  (h : ∀ i : Fin 3, IsInvertibleEdge (edgeOfSimplex
    (((ihom A).obj Y).δ i (SSet.yonedaEquiv (transposeFunctorFamily F)))))

/-- 元の全高次の三角形族を、同じ可逆三角形の全部分複体へ持ち上げる。 -/
def equivalenceTriangleFamilyLift : A ⟶ equivalenceTriangle Y :=
  fullSubcomplexLift _ F (by
    intro a i
    change IsInvertibleEdge (edgeOfSimplex (Y.δ i (triangleFunctorVertexSimplex (F.app _ a))))
    rw [triangleFunctorVertexSimplex_family]
    apply (isInvertibleEdge_congr
      (f := (edgeOfSimplex (((ihom A).obj Y).δ i
        (SSet.yonedaEquiv (transposeFunctorFamily F)))).map
          ((truncation 2).map (evaluateFunctorAt a)))
      (δ_naturality_apply (evaluateFunctorAt a) i
        (SSet.yonedaEquiv (transposeFunctorFamily F))).symm).mpr
    exact (h i).map (evaluateFunctorAt a))

/-- 同じ可逆三角形への持ち上げは、包含後に元の全高次の族を回収する。 -/
lemma equivalenceTriangleFamilyLift_ι :
    equivalenceTriangleFamilyLift F h ≫ equivalenceTriangleι Y = F := fullSubcomplexLift_ι _ _ _

/-- 同じ三角形族の各面は、元の同じ区間族への制限を包含後に厳密に回収する。 -/
lemma equivalenceTriangleFamilyLift_face_ι (i : Fin 3) :
    equivalenceTriangleFamilyLift F h ≫ equivalenceTriangleFace Y i ≫ equivalencePathι Y =
      F ≫ (pre (stdSimplex.δ i)).app Y := by
  rw [equivalenceTriangleFace_ι, ← Category.assoc,
    equivalenceTriangleFamilyLift_ι]

end SerrePositivity.InfinityCategories
