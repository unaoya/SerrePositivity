module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTrianglePointedComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorRestrictedEndpoint

/-!
概要：元の全三角形の指定比較を、同じ三辺の全 prism 空間へ写す。
方針：元の延長の包含・辺制限・厳密な底の表示変更を合成する。
規約：実延長と指定比較の値を保持。使われ方：元の右辺比較への指定自然性の適用。
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
  (w : FunctorTrianglePointedWitness T p s)
  {Q R : B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy Q R) (i : Fin 3)
  (hFace : stdSimplex.δ i ≫ T.diagram = curry H.h)
local notation "base" => (Δ[2] ◁ p) ≫ functorSimplexDiagram T.diagram
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)
local notation "hEdge" => functorTrianglePrism_edge_base T.diagram p i H hFace

/-- 元の全三角形を、底の元の辺式を保持した同じ相対 prism 空間へ制限する。 -/
def FunctorTrianglePointedWitness.edgeMap :
    w.choice ⟶ relativeFunctorSpace pointedSpaceProjection d :=
  relativeFunctorExtensionSpaceι pointedSpaceProjection base (scaffoldFirstVertex 2 ▷ C)
    (CartesianMonoidalCategory.snd Δ[0] C ≫ s ≫ pullback.fst pointedSpaceProjection F)
    w.start_projection ≫ relativeFunctorPre pointedSpaceProjection base (stdSimplex.δ i ▷ C) ≫
      eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection) hEdge)

/-- 制限した各頂点は、元の実延長の同じ辺そのものを表す。 -/
lemma FunctorTrianglePointedWitness.edgeMap_vertex (w' : FunctorTrianglePointedWitness T p s) :
    (w.edgeMap H i hFace).app _ (w.point w') = relativeFunctorVertex pointedSpaceProjection d
      ((stdSimplex.δ i ▷ C) ≫ w'.prism) (by
        rw [Category.assoc, w'.projection]; exact hEdge) := by
  have he := congrArg
    (fun z => (eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection) hEdge)).app _ z)
    (relativeFunctorPre_vertex pointedSpaceProjection base (stdSimplex.δ i ▷ C)
      w'.prism w'.projection)
  exact he.trans (relativeFunctorVertex_transport pointedSpaceProjection hEdge _ _)

/-- 同じ全三角形の指定比較を、元の同じ辺へ写した値。 -/
def FunctorTrianglePointedWitness.edgeComparison
    (hi : s ≫ leftUnstraighteningProjection F = p) :=
  VertexIso.map (w.comparison hi) (w.edgeMap H i hFace)

/-- 元の同じ二実 prism の頂点表示へ揃えた、同じ指定辺比較。 -/
def FunctorTrianglePointedWitness.prismComparison
    (hi : s ≫ leftUnstraighteningProjection F = p) :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk (w.edgeMap_vertex H i hFace w))).symm ≪≫
    w.edgeComparison H i hFace hi ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (w.edgeMap_vertex H i hFace (functorTrianglePointedCanonicalWitness T p s hi)))

end SerrePositivity.InfinityCategories.F2
