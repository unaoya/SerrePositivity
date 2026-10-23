module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleSequentialPostComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleFirstInversePostIso

/-!
概要：元の指定三角形比較の成分を、同じ実三辺の後合成の比較で厳密に表示する。
方針：三つの native 頂点式を明示し、元の三辺の値を保って同じ始点と終点へ輸送する。
規約：元の指定値と全係数を保持。使われ方：四面の六比較の相殺の具体的な入力。
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
local notation "va" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)
local notation "vb" => leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)
local notation "vc" => leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J) (Subtype.val vb) (Subtype.property vb) p
local notation "A" => functorHomotopySourceCanonicalWitness a p s hi

/-- 元の三角形比較の成分は、同じ全実三辺の指定後合成比較の合成に厳密に等しい。 -/
lemma FunctorTrianglePointedWitness.sequentialPostComparison_app_eq_threeEdges :
    (functorTriangleSequentialPostComparison T p).app
      (relativeFunctorVertex (leftUnstraighteningProjection F) p s hi) =
      functorHomotopySourcePostIso c p s hi w.longWitness ≪≫
        (functorHomotopySourcePostIso b p w.middle w.middle_projection w.secondWitness).symm ≪≫
          VertexIso.map (functorHomotopySourcePostIso a p s hi w.firstWitness).symm P := by
  let ac := functorHomotopySourceEndpointIso c p s hi w.longWitness
  let ab := functorHomotopySourceEndpointIso b p w.middle w.middle_projection w.secondWitness
  let bc := functorHomotopySourcePostIso c p s hi w.longWitness
  let bb := functorHomotopySourcePostIso b p w.middle w.middle_projection w.secondWitness
  let ba := functorHomotopySourcePostIso a p s hi w.firstWitness
  have ha := relativeFunctorPost_vertex _ _ _ (va).property p s hi
  have hb := relativeFunctorPost_vertex _ _ _ (vb).property p w.middle w.middle_projection
  have hc := relativeFunctorPost_vertex _ _ _ (vc).property p s hi
  have ht := (congrArg (fun v => (P).app (Opposite.op ⦋0⦌) v) ha).trans
    (relativeFunctorPost_vertex _ _ _ (vb).property p (A).endpoint (A).endpoint_over)
  have hi' := vertexIso_symm_heq_of_heq ab bb hb.symm rfl
    (functorHomotopySourcePostIso_heq_source b p w.middle w.middle_projection w.secondWitness).symm
  have hm := vertexIso_trans_heq_of_heq ab.symm (w.firstInverseNativeComparison hi)
    bb.symm (VertexIso.map ba.symm P) rfl hb.symm ht.symm hi'
    (w.firstInverseNativeComparison_heq_sourcePost hi)
  have h := vertexIso_trans_heq_of_heq ac (ab.symm ≪≫ w.firstInverseNativeComparison hi)
    bc (bb.symm ≪≫ VertexIso.map ba.symm P) hc.symm rfl ht.symm
    (functorHomotopySourcePostIso_heq_source c p s hi w.longWitness).symm hm
  exact eq_of_heq ((w.sequentialPostComparison_app_heq_threeEdges T p hi).trans h)

end SerrePositivity.InfinityCategories.F2
