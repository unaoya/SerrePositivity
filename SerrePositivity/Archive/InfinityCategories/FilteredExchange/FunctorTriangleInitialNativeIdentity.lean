module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleInitialComparisons

/-!
概要：元の全三角形比較の第一辺・長辺の native 始点像は、元の同じ頂点の恒等同型。
方針：初期頂点を固定した全族の定値性と、同じ指定辺比較の像を使う。
規約：指定同型の値を保持。使われ方：第一辺・長辺の指定自然性の厳密な簡約。
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

/-- 元の第一辺の指定比較の native 始点像は、同じ第一作用の頂点の恒等同型。 -/
lemma FunctorTrianglePointedWitness.firstNativeComparison_eq_refl :
    w.firstNativeComparison hi = Iso.refl _ := by
  have ha : HEq (w.firstNativeComparison hi) (VertexIso.map (w.firstPrismComparison hi)
      (functorHomotopyPrismSourceEvaluation a p ≫ HomotopyLimits.relativeFunctorPost
        (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val
        (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).property p)) :=
    vertexIsoOfEq_heq _ (functorHomotopyPrismNativeSource_vertex a p s hi w.firstWitness)
      (functorHomotopyPrismNativeSource_vertex a p s hi (z).firstWitness)
  exact eq_of_heq (ha.trans (w.prismComparison_native_heq_refl hi a 2 T.face_two
    (by apply SSet.hom_ext; intro n; rfl)))

/-- 元の長辺の指定比較の native 始点像も、同じ長辺作用の頂点の恒等同型。 -/
lemma FunctorTrianglePointedWitness.longNativeComparison_eq_refl :
    w.longNativeComparison hi = Iso.refl _ := by
  have ha : HEq (w.longNativeComparison hi) (VertexIso.map (w.longPrismComparison hi)
      (functorHomotopyPrismSourceEvaluation c p ≫ HomotopyLimits.relativeFunctorPost
        (leftUnstraighteningProjection F) (leftUnstraighteningProjection J)
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).val
        (leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)).property p)) :=
    vertexIsoOfEq_heq _ (functorHomotopyPrismNativeSource_vertex c p s hi w.longWitness)
      (functorHomotopyPrismNativeSource_vertex c p s hi (z).longWitness)
  exact eq_of_heq (ha.trans (w.prismComparison_native_heq_refl hi c 1 T.face_one
    (by apply SSet.hom_ext; intro n; rfl)))

end SerrePositivity.InfinityCategories.F2
