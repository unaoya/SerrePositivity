module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleEndpointEdges

/-!
概要：元の第一指定始域比較の逆への native 後合成を、元の作用の頂点で保持する。
方針：相対後合成の頂点式と canonical 中間頂点の厳密な一致を使う。
規約：指定比較の値を保持。使われ方：全終点比較を元の二辺の比較へ表す。
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
local notation "A" => functorHomotopySourceCanonicalWitness a p s hi
local notation "v" => leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)
local notation "P" => HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection G)
  (leftUnstraighteningProjection J) (Subtype.val v) (Subtype.property v) p

/-- 元の第一指定始域比較の逆を、同じ第二 native 作用で後合成した指定値。 -/
def FunctorTrianglePointedWitness.firstInverseNativeComparison :=
  vertexIsoOfEq
    (VertexIso.map (functorHomotopySourceEndpointIso a p s hi w.firstWitness).symm P)
    (relativeFunctorPost_vertex _ _ _ (v).property p w.middle w.middle_projection)
    (relativeFunctorPost_vertex _ _ _ (v).property p (A).endpoint (A).endpoint_over)

/-- 同じ元の canonical 中間頂点を使う二つの native 合成の頂点は厳密に一致する。 -/
lemma functorTriangleCanonical_middle_native_vertex :
    relativeFunctorVertex (leftUnstraighteningProjection J) p
      ((z).middle ≫ (v).val) (by rw [Category.assoc, (v).property, (z).middle_projection]) =
    relativeFunctorVertex (leftUnstraighteningProjection J) p
      ((A).endpoint ≫ (v).val) (by rw [Category.assoc, (v).property]; exact (A).endpoint_over) := by
  apply Subtype.ext
  exact congrArg functorVertex (congrArg (fun f => f ≫ (v).val)
    (functorTriangleCanonical_middle T p s hi))

/-- 同じ全三角形の中間像は、元の第一指定比較の逆の native 後合成の同じ値。 -/
lemma FunctorTrianglePointedWitness.middleNativeComparison_heq_firstInverseNative :
    HEq (w.middleNativeComparison hi) (w.firstInverseNativeComparison hi) :=
  (w.middleNativeComparison_heq_firstInverse hi).trans
    (vertexIsoOfEq_heq _
      (relativeFunctorPost_vertex _ _ _ (v).property p w.middle w.middle_projection)
      (relativeFunctorPost_vertex _ _ _ (v).property p (A).endpoint (A).endpoint_over)).symm

end SerrePositivity.InfinityCategories.F2
