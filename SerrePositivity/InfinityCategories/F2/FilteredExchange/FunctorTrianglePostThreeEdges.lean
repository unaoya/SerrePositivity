module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePostComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleThreeEdgeFormula

/-!
概要：全相対始域に自然な元の三角形比較の成分を、同じ全実三辺の指定比較で表示する。
方針：後合成の元の成分と指定前合成の一致を、元の三辺による表示へ合成する。
規約：指定値と全係数を保持。使われ方：同じ六辺で四面の自然な比較を照合する。
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

/-- 全相対始域に自然な指定三角形比較の元の成分を、同じ実三辺の指定比較で表示する。 -/
lemma FunctorTrianglePointedWitness.postComparison_app_heq_threeEdges :
    HEq ((functorTrianglePostComparison T p).app
      (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi))
      (functorHomotopySourceEndpointIso c p s hi w.longWitness ≪≫
        ((functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness).symm ≪≫
          w.firstInverseNativeComparison hi)) :=
  (functorTrianglePostComparison_app_heq_pre T p s hi).trans (w.specifiedTriangle_heq_threeEdges hi)

end SerrePositivity.InfinityCategories.F2
