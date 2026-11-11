module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleMiddleEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の全三角形比較の中間像と、同じ第二 native 作用の後合成を元の実頂点で表す。
方針：中間評価の頂点式と相対後合成の同じ頂点式で端点表示だけを揃える。
規約：全係数・元の指定比較を保持。使われ方：右辺の native 始点像の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s) (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "z" => functorTrianglePointedCanonicalWitness T p s hi
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J)
  (Subtype.val (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)))
  (Subtype.property (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b))) p

/-- 元の同じ全三角形比較を、元の二つの実中間頂点で評価した値。 -/
def FunctorTrianglePointedWitness.middleComparison :=
  vertexIsoOfEq (VertexIso.map (w.comparison hi) w.middleMap)
    (w.middleMap_vertex w) (w.middleMap_vertex z)

/-- 元の同じ中間比較に第二 native 作用を後合成し、元の作用の頂点へ表示を揃えた値。 -/
def FunctorTrianglePointedWitness.middleNativeComparison :=
  vertexIsoOfEq (VertexIso.map (w.middleComparison hi) P)
    (relativeFunctorPost_vertex _ _ _
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property
      p w.middle w.middle_projection)
    (relativeFunctorPost_vertex _ _ _
      (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property
      p (z).middle (z).middle_projection)

/-- 元の中間比較への native 後合成は、同じ全三角形比較の中間評価後の像そのもの。 -/
lemma FunctorTrianglePointedWitness.middleNativeComparison_heq_map :
    HEq (w.middleNativeComparison hi) (VertexIso.map (w.comparison hi) (w.middleMap ≫ P)) := by
  let ν := w.comparison hi
  have h₀ : HEq (w.middleComparison hi) (VertexIso.map ν w.middleMap) :=
    vertexIsoOfEq_heq _ (w.middleMap_vertex w) (w.middleMap_vertex z)
  have hm := vertexIso_map_heq_of_heq (w.middleComparison hi) (VertexIso.map ν w.middleMap)
    (w.middleMap_vertex w).symm (w.middleMap_vertex z).symm h₀ P
  have h₁ : HEq (w.middleNativeComparison hi) (VertexIso.map (w.middleComparison hi) P) :=
    vertexIsoOfEq_heq _
      (relativeFunctorPost_vertex _ _ _
        (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property
        p w.middle w.middle_projection)
      (relativeFunctorPost_vertex _ _ _
        (leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)).property
        p (z).middle (z).middle_projection)
  exact h₁.trans (hm.trans (heq_of_eq (vertexIso_map_comp ν w.middleMap P)))

end SerrePositivity.InfinityCategories.F2
